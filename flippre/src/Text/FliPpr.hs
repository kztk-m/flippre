{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Text.FliPpr (
  -- * Types
  FliPpr (..),
  FliPprM,
  Exp,
  In,
  Branch (..),
  PartialBij (..),
  Err (..),
  Phase (..),
  Phased,

  -- * Syntax

  -- ** Types
  FType (..),
  type D,
  type (~>),

  -- ** To wrap-up
  flippr,

  -- ** Lambda
  app,
  arg,
  (@@),

  -- ** Biased choice
  (<?),
  abort,

  -- ** Case
  case_,
  unpair,
  ununit,

  -- *** Matching
  InExp,
  Destructable (..),
  GenDestructable,

  -- ** recursive definition primitives
  share,
  local,
  mfixF,
  letrs,
  def,

  -- ** Pretty-Printing Combinators and Datatypes
  spaces,
  space,
  (<#>),
  line',
  module Text.FliPpr.Doc,

  -- ** Derived Combinators
  (<+>.),
  (</>.),
  foldPpr,
  foldPprL,
  foldPprShared,
  foldPprLShared,

  -- ** Easy Definition
  Repr (..),
  Arg (..),

  -- ** Pattern-like expressions
  module Text.FliPpr.Pat,

  -- ** Template Haskell
  un,
  branch,
  mkUn,
  pat,

  -- ** Predefined Deconstructors
  unTrue,
  unFalse,
  unNil,
  unCons,
  unLeft,
  unRight,
  unTuple3,

  -- * Finite natural numbers (mostly, imported from "fin")
  F.Fin (..),
  F.SNat (..),
  F.SNatI (..),
  F.Nat0,
  F.Nat1,
  F.Nat2,
  F.Nat3,
  F.Nat4,
  F.Nat5,
  F.Nat6,
  F.Nat7,
  F.Nat8,
  F.Nat9,

  -- * Evaluator
  pprMode,
  parsingMode,
  parsingModeWith,
  parsingModeSP,
  CommentSpec (..),
  BlockCommentSpec (..),
  G.Grammar,

  -- * Utils
  textAs,
  RS.RSet,
  Fixity (..),
  Assoc (..),
  Prec,
  opPrinter,
  is,
  isMember,
  convertInput,
)
where

import qualified Data.Fin as F
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import qualified Data.RangeSet.List as RS
import qualified Data.Set as S
import qualified Data.Type.Nat as F

import GHC.Stack (HasCallStack, withFrozenCallStack)

import Text.FliPpr.Doc
import qualified Text.FliPpr.Grammar as G
import Text.FliPpr.Grammar.Err
import Text.FliPpr.Internal.ParserGeneration
import Text.FliPpr.Internal.PrettyPrinting
import Text.FliPpr.Pat
import Text.FliPpr.Primitives
import Text.FliPpr.TH

import Data.Kind (Type)
import Data.Void (Void)
import qualified Defs
import GHC.Generics (Generic (..), K1 (..), M1 (..), U1 (..), V1, (:*:) (..), (:+:) (..))
import Text.FliPpr.Automaton as A
import Text.Printf (printf)

-- | In pretty-printing, '<+>.' behaves as '<+>', but in parser construction,
--   it behaves as '<>'.
(<+>.) :: Exp s v D -> Exp s v D -> Exp s v D
x <+>. y = x <#> nespaces' <#> y

-- | In pretty-printing, '</>.' behaves as '</>', but in parser construction,
--   it behaves as '<>'.
(</>.) :: Exp s v D -> Exp s v D -> Exp s v D
x </>. y = x <#> line' <#> y

infixr 4 <+>.

infixr 4 </>.

-- | @is c f@ is a branch for the case where the input is equal to @c@.
--
-- This will be used with 'case_' as:
--
-- > case_ x [ is '0' ..., is '1' ... , ... ]
-- is :: (FliPprE arg exp, Eq c, Show c) => c -> E exp r -> Branch (A arg) (E exp) c r
is :: (Show a, Eq a) => a -> Exp s v t -> Branch (In v) (Exp s v) a t
is c f =
  PartialBij
    ("is " ++ show c)
    (\x -> if x == c then Just () else Nothing)
    (\_ -> Just c)
    `Branch` (`ununit` f)

-- | @isMember cs f@ is a branch for the case where the input belongs to the set @cs@.
-- isMember :: (Show c, Ord c) => RS.RSet c -> (A arg c -> E exp r) -> Branch (A arg) (E exp) c r
isMember :: (Show a, Ord a) => RS.RSet a -> (In v a -> Exp s v t) -> Branch (In v) (Exp s v) a t
isMember cs f =
  PartialBij
    ("isMember " ++ show cs)
    (\x -> if x `RS.member` cs then Just x else Nothing)
    (\x -> if x `RS.member` cs then Just x else Nothing)
    `Branch` f

-- Converts an input by using a bijection.
--  convertInput :: (FliPprE arg exp) => PartialBij a b -> A arg a -> (A arg b -> E exp r) -> E exp r
convertInput :: PartialBij a b -> In v a -> (In v b -> Exp s v r) -> Exp s v r
convertInput pij a r = case_ a [pij `Branch` r]

-- | Precedence. An operator with a higher precedence binds more tighter.
type Prec = Int

-- | Fixity is a pair of associativity and precedence.
data Fixity = Fixity Assoc Prec

-- | Operator's associativity.
data Assoc
  = -- | left associative
    AssocL
  | -- | right associative
    AssocR
  | -- | non-associative
    AssocN

-- | A pretty-printer for binary-operator expressions such as @e1 + e2@.
-- A typical use is:
--
-- > rec pprExp <- define $ \i e -> case_ i [
-- >         ...
-- >         unAdd $ \e1 e2 -> opPrinter (\d1 d2 -> d1 <+>. text "+" <+>. d2) (flip pprExp e1) (flip pprExp e2),
-- >         ... ]
opPrinter ::
  (DocLike d, Ord n, Num n) =>
  Fixity
  -> (d -> d -> d)
  -> (n -> d)
  -- ^ precedence printer for the first operand
  -> (n -> d)
  -- ^ precedence printer for the second operand
  -> (n -> d)
opPrinter (Fixity a opPrec) opD ppr1 ppr2 =
  let (dl, dr) = case a of
        AssocL -> (0, 1)
        AssocR -> (1, 0)
        AssocN -> (0, 0)
      d = opD (ppr1 (fromIntegral opPrec + dl)) (ppr2 (fromIntegral opPrec + dr))
      pd = parens d
  in  \k -> if k > fromIntegral opPrec then pd else d

$(mkUn ''Bool)
$(mkUn ''[])
$(mkUn ''Either)
$(mkUn ''(,,))

-- | A type to ensure that @a@ appears in a FliPpr expression.
--
-- > type InExp s v a = forall r. (a -> Exp s v r) -> Exp s v r
type InExp s v a = forall r. (a -> Exp s v r) -> Exp s v r

class GenDestructable f where
  type GenDecomposed v f :: Type
  matchGen :: In v (f p) -> InExp s v (GenDecomposed v f)

instance GenDestructable V1 where
  type GenDecomposed v V1 = Void
  matchGen i _ = case_ i [] -- really ok?

instance GenDestructable U1 where
  type GenDecomposed v U1 = ()
  matchGen i k = convertInput unit2unit i $ \i' -> ununit i' (k ())
    where
      unit2unit :: PartialBij (U1 p) ()
      unit2unit = PartialBij "unit2unit" (const $ pure ()) (const $ pure U1)

instance (GenDestructable f, GenDestructable g) => GenDestructable (f :*: g) where
  type GenDecomposed v (f :*: g) = (GenDecomposed v f, GenDecomposed v g)
  matchGen i k = convertInput pair2pair i $ \i' -> unpair i' $ \x y -> matchGen x $ \x' -> matchGen y $ \y' -> k (x', y')
    where
      pair2pair :: PartialBij ((f :*: g) p) (f p, g p)
      pair2pair = PartialBij "pair2pair" (\(x :*: y) -> pure (x, y)) (\(x, y) -> pure (x :*: y))

instance (GenDestructable f, GenDestructable g) => GenDestructable (f :+: g) where
  type GenDecomposed v (f :+: g) = Either (GenDecomposed v f) (GenDecomposed v g)
  matchGen i k = convertInput sum2sum i $ \i' ->
    case_
      i'
      [ unLeft $ \x -> matchGen x (k . Left)
      , unRight $ \y -> matchGen y (k . Right)
      ]
    where
      sum2sum :: PartialBij ((f :+: g) p) (Either (f p) (g p))
      sum2sum = PartialBij "sum2sum" (pure . ff) (pure . ffi)

      ff (L1 x) = Left x
      ff (R1 y) = Right y

      ffi (Left x) = L1 x
      ffi (Right y) = R1 y

instance GenDestructable (K1 i c) where
  type GenDecomposed v (K1 i c) = In v c -- stop deconstruction
  matchGen = convertInput unK1I
    where
      unK1I :: PartialBij (K1 i c p) c
      unK1I = PartialBij "unK1" (pure . unK1) (pure . K1)

instance (GenDestructable f) => GenDestructable (M1 i t f) where
  type GenDecomposed v (M1 i t f) = GenDecomposed v f
  matchGen i k = convertInput unM1I i $ \i' -> matchGen i' k
    where
      unM1I :: PartialBij (M1 i t f p) (f p)
      unM1I = PartialBij "unM1I" (pure . unM1) (pure . M1)

class Destructable r where
  type Decomposed v r :: Type
  type Decomposed v r = GenDecomposed v (Rep r)

  -- | 'match' enables us to Haskell's @case@ expression to perform case
  -- analysis in FliPpr.
  --
  -- For example, one can write:
  --
  -- > match xs $ \case
  -- >    Left () -> e
  -- >    Right (y,ys) -> f y ys
  --
  -- instead of
  --
  -- > case_ xs
  -- >    [ unNil e
  -- >    , unCons $ \y ys -> f y ys
  -- >    ]
  --
  -- The default implementation uses the sum-of-product representation of a datatype via 'Generic'.
  --
  -- > > data T a = L | O a | B a (T a) (T a) deriving Generic
  -- > > instance Destructable (T a)
  -- > > :k! Decomposed v (T a)
  -- > Decomposed v (T a) :: *
  -- > = Either () (Either (In v a) (In v a, (In v (T a), In v (T a))))
  --
  -- The very core idea is inspired by the paper, though the details are not the same.
  -- Trevor L. McDonell, et al. Embedding Pattern Matching, Haskell Symposium 2022. pp 123-136.
  match :: In v r -> InExp s v (Decomposed v r)
  default match :: (Generic r, GenDestructable (Rep r), Decomposed v r ~ GenDecomposed v (Rep r)) => In v r -> InExp s v (Decomposed v r)
  match i k = convertInput fromI i $ \i' -> matchGen i' k
    where
      fromI :: (Generic r) => PartialBij r (Rep r p)
      fromI = PartialBij "from" (pure . GHC.Generics.from) (pure . GHC.Generics.to)
instance Destructable [a] where
  type Decomposed v [a] = Either () (In v a, In v [a])
  match = matchList

instance Destructable (a, b) where
  type Decomposed v (a, b) = (In v a, In v b)
  match = matchPair

instance Destructable (Either a b) where
  type Decomposed v (Either a b) = Either (In v a) (In v b)
  match = matchEither

instance Destructable Bool where
  type Decomposed v Bool = Bool
  match = matchBool

matchList :: In v [a] -> InExp s v (Either () (In v a, In v [a]))
matchList x k =
  case_
    x
    [ unNil $ k (Left ())
    , unCons $ curry (k . Right)
    ]

matchEither :: In v (Either a b) -> InExp s v (Either (In v a) (In v b))
matchEither x0 k =
  case_
    x0
    [ unLeft $ k . Left
    , unRight $ k . Right
    ]

matchPair :: In v (a, b) -> InExp s v (In v a, In v b)
matchPair xy = unpair xy . curry

matchBool :: In v Bool -> InExp s v Bool
matchBool b k = case_ b [unTrue $ k True, unFalse $ k False]

-- | @textAs x r@ serves as @text x@ in pretty-printing, but
-- in parsing it serves as @r@ of which parsing result is used to update @x$.
textAs :: (HasCallStack, Phased s) => In v [Char] -> A.DFA Char -> Exp s v D
textAs a m = withFrozenCallStack (textAs' m a)

textAs' :: (HasCallStack, Phased s) => A.DFA Char -> In v [Char] -> Exp s v D
textAs' (A.DFAImpl i qs fs tr) = local $
  letrs (S.toList qs) $ \f ->
    def
      ( \q s ->
          case_
            s
            [ unNil $ if q `S.member` fs then text "" else abort
            , unCons $ \c r ->
                case_ c [isMember' cs $ \c' -> charAs c' cs <#> f q' r | (cs, q') <- fromMaybe [] $ M.lookup q tr]
            ]
      )
      $ return (f i)
  where
    isMember' cs k =
      case isMember cs k of
        Branch (PartialBij p f fi) h ->
          let p'
                | RS.isFull cs = "_"
                | [(c, c')] <- rlist, c' == c = "is " ++ show c
                | [(c, c')] <- rlistc, c' == c = printf "isMember complement(singleton %c)" 'c'
                | otherwise = p
                where
                  rlist = RS.toRangeList cs
                  rlistc = RS.toRangeList (RS.complement cs)
          in  Branch (PartialBij p' f fi) h

-- | A list printer.
--
-- [NOTE] We are not able to have `mapPpr :: ... => (A arg i -> E exp D) -> A arg [i] -> FliPprM [E exp D]`.
-- In FliPpr, one can only define recursive printers that can be interpreted as context-free grammars.
-- By returning lists depending the input AST, we can do anything with lists---in particular, we can
-- define different printers for different indices. This is beyond context-free.
foldPpr :: (Phased s) => (In v a -> Exp s v t -> Exp s v t) -> Exp s v t -> In v [a] -> Exp s v t
foldPpr c n = local $ foldPprShared c n

-- | If 'foldPpr' is used with the same arguments more than once, the following version
--   is more efficient.
--
--  > do p <- foldPprShared (...) (...)
--  >    ... p xs ... p ys ...
foldPprShared :: (Phased s) => (In v a -> Exp s v t -> Exp s v t) -> Exp s v t -> FliPprM s v (In v [a] -> Exp s v t)
foldPprShared c n =
  Defs.letr $ \f ->
    def
      ( arg $ \es0 ->
          case_
            es0
            [ unNil n
            , unCons $ \e es -> c e (f `app` es)
            ]
      )
      $ pure (app f)

-- | A list printer that treats the last element specially.
--
-- For example, the following prints lists separated by commas
-- > foldPprL (\a d -> pprElem a <> text "," <+>. d) pprElem (text "")
foldPprL :: (Phased s) => (In v a -> Exp s v t -> Exp s v t) -> (In v a -> Exp s v t) -> Exp s v t -> In v [a] -> Exp s v t
foldPprL c s n = local $ foldPprLShared c s n

-- | If 'foldPprL' is used with the same arguments more than once, the following version
--   is more efficient.
foldPprLShared :: (Phased s) => (In v a -> Exp s v t -> Exp s v t) -> (In v a -> Exp s v t) -> Exp s v t -> FliPprM s v (In v [a] -> Exp s v t)
foldPprLShared c s n =
  Defs.letr $ \f ->
    Defs.letr $ \g ->
      def
        ( arg $ \es0 ->
            case_
              es0
              [ unNil n
              , unCons $ \e es -> g `app` e `app` es
              ]
        )
        >>> def
          ( arg $ \e0 -> arg $ \es0 ->
              case_
                es0
                [ unNil (s e0)
                , unCons $ \e es -> c e0 (g `app` e `app` es)
                ]
          )
        $ pure (app f)
  where
    (>>>) = flip (.)
