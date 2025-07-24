{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
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

import qualified Defs
import Text.FliPpr.Automaton as A

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

-- defines :: (FliPprD arg exp, Repr arg exp t r, F.SNatI n) => F.SNat n -> (FinNE n -> r) -> FliPprM exp (FinNE n -> r)
-- defines _ f = do
--   let ks = [minBound .. maxBound]
--   rs <- mapM (define . f) ks
--   let table = M.fromList $ zip ks rs
--   return $ \k -> case M.lookup k table of
--     Just m  -> m
--     Nothing -> error "defines_: Cannot happen."

-- -- |
-- -- @defineR (k1,k2)@ is the same as @defines [k1..k2]@, but a bit more efficient. x
-- {-# SPECIALIZE defineR ::
--   (FliPprD arg exp, Repr arg exp t r) => (Int, Int) -> (Int -> r) -> DefM (E exp) (Int -> r)
--   #-}
-- defineR :: (Eq k, Ord k, Enum k, FliPprD arg exp, Repr arg exp t r) => (k, k) -> (k -> r) -> DefM (E exp) (k -> r)
-- defineR (k1, k2) f = do
--   let (m1, m2) = if k1 < k2 then (k1, k2) else (k2, k1)
--   let ks = [m1 .. m2]
--   rs <- mapM (define . f) ks
--   let table = M.fromAscList $ zip ks rs
--   return $ \k -> case M.lookup k table of
--     Just m -> m
--     Nothing -> error "defineR: out of bounds"

-- -- |
-- -- @defines [k1,...,kn] f@ is equivalent to:
-- --
-- -- @
-- --   do  fk1 <- define (f k1)
-- --       ...
-- --       fk2 <- define (f k2)
-- --       return $ \k -> lookup k [(k1,fk1),...,(k2,fk2)]
-- -- @
-- {-# SPECIALIZE defines ::
--   (FliPprD arg exp, Repr arg exp t r) => [Int] -> (Int -> r) -> DefM (E exp) (Int -> r)
--   #-}
-- defines :: (Eq k, Ord k, FliPprD arg exp, Repr arg exp t r) => [k] -> (k -> r) -> DefM (E exp) (k -> r)
-- defines ks f = do
--   rs <- mapM (define . f) ks
--   let table = M.fromList $ zip ks rs
--   return $ \k -> case M.lookup k table of
--     Just m -> m
--     Nothing -> error "defines: out of bounds"

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
opPrinter (Fixity a opPrec) opD ppr1 ppr2 k =
  let (dl, dr) = case a of
        AssocL -> (0, 1)
        AssocR -> (1, 0)
        AssocN -> (0, 0)
  in  ifParens (k > fromIntegral opPrec) $ opD (ppr1 (fromIntegral opPrec + dl)) (ppr2 (fromIntegral opPrec + dr))
  where
    ifParens b = if b then parens else id

$(mkUn ''Bool)
$(mkUn ''[])
$(mkUn ''Either)
$(mkUn ''(,,))

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
                case_ c [isMember cs $ \c' -> charAs c' cs <#> f q' r | (cs, q') <- fromMaybe [] $ M.lookup q tr]
            ]
      )
      $ return (f i)

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
