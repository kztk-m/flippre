{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Text.FliPpr.Internal.Type (
  FType (..),
  type D,
  type (~>),
  In,
  FliPprE (..),
  FliPprD,
  A (..),
  E (..),
  FliPpr (..),
  Branch (..),
  PartialBij (..),
  flippr,
  arg,
  app,
  (@@),
  abort,
  charAs,
  case_,
  unpair,
  ununit,
  Text.FliPpr.Internal.Type.line',
  Text.FliPpr.Internal.Type.space,
  spaces,
  nespaces,
  nespaces',
  (<?),
  hardcat,
  (<#>),
  Repr (..),
  FliPprM,
  mfixF,
  -- letr, letrs,
  Defs.letrs,
  def,
  share,
  local,
  FinNE,
  reifySNat,
  -- Wit (..),

  Defs.Arg (..), -- Defs.Convertible,
  Defs,
)
where

import Control.Applicative (Const (..))
import Control.Monad (forM)
import Control.Monad.State hiding (lift)
import Data.Coerce (coerce)
import qualified Data.Fin as F
import Data.Kind (Type)
import qualified Data.Type.Nat as F
import Data.Typeable (Proxy (..))

import qualified Prettyprinter as D

import Defs (Defs)
import qualified Defs

import Text.FliPpr.Doc as DD

import Control.Arrow (first)

import Data.Function.Compat (applyWhen)
import qualified Data.RangeSet.List as RS
import Data.String (IsString (..))
import GHC.Stack (HasCallStack)

-- | The kind for FliPpr types.
data FType = FTypeD | Type :~> FType

-- | Unticked synonym for :~> used for readability.
type a ~> b = a ':~> b

-- | Unticked synonym for FTypeD
type D = 'FTypeD

type In a = Eq a

-- | Partial bijections between @a@ and @b@.
data PartialBij a b
  = PartialBij
      !String
      -- ^ field used for pretty-printing
      !(a -> Maybe b)
      -- ^ forward transformation
      !(b -> Maybe a)
      -- ^ backward transformation

-- | A datatype represents branches.
data Branch arg exp a (t :: FType)
  = -- | the part @arg b -> exp t@ must be a linear function
    forall b. (In b) => Branch (PartialBij a b) (arg b -> exp t)

-- | A finally-tagless implementation of FliPpr expressions.
--   The API is only for internal use.
class FliPprE (arg :: Type -> Type) (exp :: FType -> Type) | exp -> arg where
  fapp :: (In a) => exp (a ~> t) -> arg a -> exp t
  farg :: (In a) => (arg a -> exp t) -> exp (a ~> t)

  fcase :: (In a) => arg a -> [Branch arg exp a t] -> exp t

  funpair :: (In a, In b) => arg (a, b) -> (arg a -> arg b -> exp t) -> exp t
  fununit :: arg () -> exp t -> exp t

  fbchoice :: exp D -> exp D -> exp D

  -- Output character as is, if it is contained in the given set
  fcharAs :: arg Char -> RS.RSet Char -> exp D

  ftext :: String -> exp D

  fabort :: (HasCallStack) => exp D -- throws an error in pretty-printing, accepts no strings in parsing

  fempty :: exp D
  fcat :: exp D -> exp D -> exp D

  -- For optimization purpose.
  fspace :: exp D
  fspaces :: exp D

  fline :: exp D -- translated to @text " " <> spaces@ in parsing
  flinebreak :: exp D -- translated to @spaces@ in parsing

  fline' :: exp D -- (fline `fbchoice` empty)
  fnespaces' :: exp D -- ((fspace `fcat` fspaces) `fbchoice` empty)

  falign :: exp D -> exp D
  fgroup :: exp D -> exp D
  fnest :: Int -> exp D -> exp D

type FliPprD arg exp = (Defs exp, FliPprE arg exp)

-- -- | A finally-tagless implementation of FliPpr expressions
-- --   that can contain recursive definictions.
-- --
-- --   Again, the APIs are only for intenral use.
-- class (FliPprE arg exp, MonadFix m) => FliPprD m arg exp | exp -> arg, exp -> m where
--   -- Using ffix to define a recursion would not be a good idea.
--   -- The information is used to define a grammar generation that is
--   -- to be used in "parsing" evaluation.
--   --
--   -- To use Earley or Frost's parser combinators it suffices to mark
--   -- body of recursive functions. This is much more convient as
--   -- we can use grammars via recursive do notations.
--   --
--   -- If such a "marking" approach would suffice for some other grammar manipulations such
--   -- as left recursion elimination or injectivity analysis, first character extraction and so on.
--   -- Then, we will use "marking" approach instead of "ffix".
--   --
--   -- By 2017-11-18 kztk:
--   -- It turns out that "marking" approach is not useful to define local definitions.
--   -- The local defintions are specially important for FliPpr, as we can
--   -- define ``inlinable'' functions. A typical example is @manyParens@, a
--   -- function to annotate a position to which arbitrary number of parens can be
--   -- placed around. By @ffix@, such a function is easy to define.
--   --
--   -- @
--   -- manyParens :: FliPpr arg exp => exp D -> exp D
--   -- manyParens d = ffix (\x -> d <|> parens x)
--   -- @
--   --
--   -- However, this is hard to achieve by using the "marking" approach, as
--   -- it can only define global definitions.
--   --
--   -- Thus, we many need both or use "marking" as a compromised alternative syntax.
--   -- It seems to me that we cannot directly converted it to @ffix@ with using
--   -- some compromising (Data.Dynamic, for example).
--   --
--   -- Anyway, @ffix@ is more general, and due to free variables, we cannot convert
--   -- it to "marking" in general. Let's have both at this level.
--   --
--   -- By kztk @ 2017-11-25
--   --
--   -- It seems to me that it is not that straightforward to define the semantics of
--   -- marking. Making a definition complex would be a not a good idea, and
--   -- mutual recursions that are hard to define by 'ffix' would not appear so oftenly.
--   --
--   -- Tentatively, we removed the marking function.
--   --
--   -- By kztk @ 2017-11-26
--   -- Having single recursion unbearablely slow and not useful at all.
--   -- The above description was wrong, and the following definition would suffice.
--   --
--   -- @
--   -- manyParens d = local $ do rec r <- rule $ d <? parens r
--   --                           return r
--   -- @
--   --
--   --
--   -- By kztk @ 2017-11-26
--   -- I find that using @rule@ has a problem on pretty-printing interpretation.
--   -- Thus, I revisited usual ffix. We cannot avoid considering general mutual
--   -- recursions as below.
--   --
--   -- ffix  :: (exp t -> exp t) -> exp t
--   --
--   --
--   -- By kztk @ 2017-12-22
--   -- Changed its type from Oleg's comment.
--   --
--   -- ffix :: Container2 f => f (Rec f exp) -> CPS exp (f exp)
--   -- flet :: exp t -> CPS exp (exp t)
--   -- flet = return
--   --
--   -- By kztk @ 2018-01-01
--   --
--   -- Changed its type to
--   fshare :: exp t -> m (exp t)
--   flocal :: m (exp t) -> exp t

-- | @A arg a@ represents an input of a pretty-printer in FliPpr. ("A" stands for "a"rgument.)
-- Here, @a@ ranges over Haskell types.
-- The value of this type must be used linearly to ensure that a resulting parser can recover this information.
--
-- Internally, this is just a newtype wrapper for @arg a@. Having 'A' is handy for declaring type class instances.
newtype A (arg :: Type -> Type) (a :: Type) = A {unA :: arg a}

-- | @E exp t@ represents a pretty-printing expression in FliPpr. ("E" stands for "e"xpression.)
-- Unlike @A arg a@, @t@ ranges over 'FType' instead of 'Type'.
--
-- Internally, this is just a newtype wrapper for @exp a@. Having 'E' is handy for declaring type class instances.
newtype E (exp :: FType -> Type) (t :: FType) = E {unE :: exp t}

-- | A newtype wrapper for the FliPpr expression type: @forall arg exp. (FliPprD arg exp) => exp t@.
newtype FliPpr t = FliPpr (forall arg exp. (FliPprD arg exp) => exp t)

-- | A monad convenient for sharing and recursive definitions.
type FliPprM exp = Defs.DefM (E exp)

-- | Make a closed FliPpr definition. A typical use is:
--
--   > flippr $ do
--   >   rec ppr <- share $ arg $ \i -> ...
--   >   return ppr
flippr :: (forall arg exp. (FliPprD arg exp) => FliPprM exp (E exp t)) -> FliPpr t
flippr x = FliPpr (unE $ Defs.local x)

-- | Indicating that there can be zero-or-more spaces in parsing.
--   In pretty-printing, it is equivalent to @text ""@.
{-# INLINEABLE spaces #-}
spaces :: (FliPprE arg exp) => E exp D
spaces = (coerce :: exp D -> E exp D) fspaces

-- | In pretty-printing, it works as @text " "@. In parsing
--   it behaves a single space.
{-# INLINEABLE space #-}
space :: (FliPprE arg exp) => E exp D
space = (coerce :: exp D -> E exp D) fspace

-- | For internal use. Use '<+>'.
{-# INLINEABLE nespaces #-}
nespaces :: (FliPprE arg exp) => E exp D
nespaces = Text.FliPpr.Internal.Type.space <#> spaces

-- | For internal use. Use '<+>.'.
{-# INLINEABLE nespaces' #-}
nespaces' :: (FliPprE arg exp) => E exp D
nespaces' = (coerce :: exp D -> E exp D) fnespaces'

-- | Similar to 'line', but it also accepts the empty string in parsing.
{-# INLINEABLE line' #-}
line' :: (FliPprE arg exp) => E exp D
line' = (coerce :: exp D -> E exp D) fline'

{-# INLINEABLE abort #-}

-- | In pretty-printing 'abort' throws an error. In parsing, it accepts no strings.
abort :: (FliPprE arg exp, HasCallStack) => E exp D
abort = (coerce :: exp D -> E exp D) fabort

-- | @arg@ represents a function in FliPpr.
-- @f@ of @arg f@ must be a linear function: @f@ must use its input exactly once.
--
-- Internally, it is a wrapper for the method 'farg' of 'FliPprE'.
{-# INLINEABLE arg #-}
arg :: (In a, FliPprE arg exp) => (A arg a -> E exp t) -> E exp (a ~> t)
arg =
  ( coerce ::
      ((arg a -> exp t) -> exp (a ~> t))
      -> (A arg a -> E exp t)
      -> E exp (a ~> t)
  )
    farg

-- | Application in FliPpr. Observed that the application is restricted to @A arg a@-typed values.
{-# INLINEABLE app #-}
app :: (In a, FliPprE arg exp) => E exp (a ~> t) -> A arg a -> E exp t
app =
  ( coerce ::
      (exp (a ~> t) -> arg a -> exp t)
      -> (E exp (a ~> t) -> A arg a -> E exp t)
  )
    fapp

-- | A synonym for 'app'. A FliPpr version of '$'.
{-# INLINE (@@) #-}
(@@) :: (In a, FliPprE arg exp) => E exp (a ~> t) -> A arg a -> E exp t
(@@) = app

infixr 0 @@

-- | Prints a 'Char' ensuring the char is in the given set.
charAs :: (FliPprE arg exp) => A arg Char -> RS.RSet Char -> E exp D
charAs =
  ( coerce ::
      (arg Char -> RS.RSet Char -> exp D)
      -> (A arg Char -> RS.RSet Char -> E exp D)
  )
    fcharAs

-- | case branching.
{-# INLINEABLE case_ #-}
case_ :: (In a, FliPprE arg exp) => A arg a -> [Branch (A arg) (E exp) a r] -> E exp r
case_ =
  ( coerce ::
      (arg a -> [Branch arg exp a r] -> exp r)
      -> A arg a
      -> [Branch (A arg) (E exp) a r]
      -> E exp r
  )
    fcase

-- | A CPS style conversion from @A arg (a,b)@ to a pair of @A arg a@ and @A arg b@.
--   A typical use of 'unpair' is to implement (invertible) pattern matching in FliPpr.
--   To guarantee invertibility, @k@ of @unpair x k@ must be a linear function.
--
--   'Language.FliPpr.TH' provides 'un' and 'branch'. By using these functions,
--   one can avoid using a bit awkward 'unpair' explicitly.
{-# INLINEABLE unpair #-}
unpair :: (In a, In b, FliPprE arg exp) => A arg (a, b) -> (A arg a -> A arg b -> E exp r) -> E exp r
unpair =
  ( coerce ::
      (arg (a, b) -> (arg a -> arg b -> exp r) -> exp r)
      -> (A arg (a, b) -> (A arg a -> A arg b -> E exp r) -> E exp r)
  )
    funpair

-- | An explicit disposal of `A arg ()`, required for the invertibility guarantee.
{-# INLINEABLE ununit #-}
ununit :: (FliPprE arg exp) => A arg () -> E exp r -> E exp r
ununit =
  ( coerce ::
      (arg () -> exp r -> exp r)
      -> A arg ()
      -> E exp r
      -> E exp r
  )
    fununit

-- | Biased choice. @a <? b = a@ in parsing, but it accepts strings indicated by both @a@ and @b$ in parsing.
(<?) :: (FliPprE arg exp) => E exp D -> E exp D -> E exp D
(<?) =
  ( coerce ::
      (exp D -> exp D -> exp D)
      -> E exp D
      -> E exp D
      -> E exp D
  )
    fbchoice

infixr 4 <?

instance (Defs.Defs e) => Defs.Defs (E e) where
  newtype D (E e) as a = RE (Defs.D e as a)

  -- liftDS (E x) = RE (Defs.liftDS x)
  liftD = coerce (Defs.liftD :: e a -> Defs.D e '[] a)

  -- unliftDS (RE x) = E (Defs.unliftDS x)
  unliftD = coerce (Defs.unliftD :: Defs.D e '[] a -> e a)
    where
      _ = RE -- just to suppress unused constructor RE, which is indeed used via coerce.

  -- consDS (E r1) (RE r2) = RE (Defs.consDS r1 r2)
  consD = coerce (Defs.consD :: e a -> Defs.D e as b -> Defs.D e (a : as) b)

  --  unpairRules (RE e) k = RE $ unpairRules e (coerce k)
  -- letrDS h = RE $ Defs.letrDS (coerce h)
  letrD = coerce (Defs.letrD :: (e a -> Defs.D e (a : as) b) -> Defs.D e as b)

-- |
-- The type class 'Repr' provides the two method 'toFunction' and 'fromFunction', which
-- perform interconversion between FliPpr functions and Haskell functions.
class Repr (arg :: Type -> Type) exp (t :: FType) r | exp -> arg, r -> arg exp t where
  toFunction :: E exp t -> r
  -- ^ @toFunction :: E exp (a1 ~> ... ~> an ~> D) -> A arg a1 -> ... -> A arg an -> E exp D@

  fromFunction :: r -> E exp t
  -- ^ @fromFunction :: (A arg a1 -> ... -> A arg an -> E exp D) -> E exp (a1 ~> ... ~> an ~> D)@

instance (FliPprE arg exp) => Repr arg exp t (E exp t) where
  toFunction = id
  fromFunction = id

instance (FliPprE arg exp, Repr arg exp t r, In a) => Repr arg exp (a ~> t) (A arg a -> r) where
  toFunction f = \a -> toFunction (f `app` a)
  fromFunction k = arg (fromFunction . k)

-- | A restricted version of 'mfix'. Use 'Text.FliPpr.MFix' to export this function as 'mfix', which
-- supposed to be used with @RecursiveDo@/@RebindableSyntax@ (and @QualifiedDo@ in future).
mfixF :: (Defs.Arg (E f) a) => (a -> FliPprM f a) -> FliPprM f a
mfixF = Defs.mfixDefM

-- type DefsF exp = Defs.DTypeVal (E exp)

-- -- | A specialized version of 'letr', which would be useful for defining mutual recursions.

--- Typical usage:
--  @
--  letr $ \f -> def fdef $
--  letr $ \g -> def gdef $
--    code_using_f_and_g
--  @
--
--  @
--  letr $ \f -> letr $ \g ->
--    -- f and g can be mutualy dependent
--    def fdeF >>>
--    def gdef $
--    code_using_f_and_g
--  @
--

-- letr :: Defs.Arg (E f) t => (t -> FliPprM f (t, r)) -> FliPprM f r
-- letr = Defs.letr

-- -- letr :: (Repr arg exp ft rep, FliPprD arg exp) => (rep -> FliPprM exp (rep, r)) -> FliPprM exp r
-- -- letr h = Defs.letr $ \x -> do
-- --   (d, r) <- h (toFunction x)
-- --   return (fromFunction d, r)

-- -- not efficient for large list
-- -- letrs :: (Repr arg exp ft rep, FliPprD arg exp, Eq k) => [k] -> ((k -> rep) -> FliPprM exp (k -> rep, r)) -> FliPprM exp r
-- letrs :: (Eq k, Defs.Arg (E f) t) => [k] -> ((k -> t) -> FliPprM f (k -> t, r)) -> FliPprM f r
-- letrs [] f = snd <$> f (const $ error "letrs: out of bounds")
-- letrs (k:ks) f = letr $ \f1 -> letrs ks $ \frest -> do
--   (rf, rest) <- f $ \k' -> if k' == k then f1 else frest k'
--   return (rf, (rf k, rest))

-- letrs = go []
--   where
--     unJust (Just x) = x
--     unJust Nothing  = "letrs: out of bounds"

-- | Useful combinator that can be used with 'letr'.
--
-- > letr $ \a -> letr $ \b ->
-- >         def body_a >>>
-- >         def body_b $
-- >         code_using_a_and_b
--
-- However, in most situations, using @RecursiveDo@ is much convenient.
--
-- > do rec a <- share body_a
-- >    rec b <- share body_b
-- >    code_using_a_and_b
-- >   where
-- >     mfix = mfixF
def :: (Functor m) => a -> m b -> m (a, b)
def a b = (a,) <$> b

-- | Sharing a computation. Roughly speaking, a (generalized) "let" in FliPpr.
--
-- For example, the following code has is inefficient in parsing as it
-- copies the productions corresponding to @e@.
--
-- > ... e ... e ...
--
-- In contrast, the following code share the productions to @e@.
--
-- > do v <- share e
-- >    ... v ... v ...
share :: (Defs.Arg (E f) r) => r -> FliPprM f r
share e = Defs.letr $ \x -> return (e, x)

-- | Localize declarations. There is a performance caveat: 'local' cancels sharing instroduced by 'share'.
--   Similarly to @e@ of @(let x = e in x) + (let x = e in x)@ is evaluated twice,
--   @... local (do {x <- share e; pure x}) ... local (do {x <- share e; pure x}) ...@ invovles
--   the productions correspoding @e@ twice.
local :: (Repr arg exp ft rep, FliPprD arg exp) => FliPprM exp rep -> rep
local = toFunction . Defs.local . fmap fromFunction

instance (Defs.Defs exp) => Defs.Arg (E exp) (E exp a) where
  letr f = Defs.letr $ fmap (first Defs.Tip) . f . Defs.unTip

-- One-level unfolding to avoid overlapping instances.
instance (FliPprE arg exp, In a, Repr arg exp t r, Defs.Defs exp) => Defs.Arg (E exp) (A arg a -> r) where
  letr f = Defs.letr $ fmap (first fromFunction) . f . toFunction

-- | FinNE n represents {0,..,n} (NB: n is included)
type FinNE n = F.Fin ('F.S n)

reifySNat :: forall n r. (Integral n) => n -> (forall m. (F.SNatI m) => F.SNat m -> r) -> r
reifySNat n k = F.reify (fromIntegral n) $ \(_ :: Proxy m) -> k (F.snat :: F.SNat m)

-- | Unlike '(<>)' that allows spaces between concatenated elementes in parsing,
--   'hardcat' does not allow such extra spaces in parsing.
{-# INLINEABLE hardcat #-}
hardcat :: (FliPprE arg exp) => E exp D -> E exp D -> E exp D
hardcat (E x) (E y) = E (fcat x y)

-- | A better syntax for `hardcat`.
{-# INLINE (<#>) #-}
(<#>) :: (FliPprE arg exp) => E exp D -> E exp D -> E exp D
(<#>) = hardcat

infixr 5 <#>

instance (D ~ t, FliPprE arg exp) => Semigroup (E exp t) where
  (<>) x y = x `hardcat` (spaces `hardcat` y)

instance (D ~ t, FliPprE arg exp) => IsString (E exp t) where
  fromString = E . ftext

-- | We can use pretty-printing combinators defined in 'Text.FliPpr.Doc' also for FliPpr expressions.
instance (D ~ t, FliPprE arg exp) => DD.DocLike (E exp t) where
  empty = E fempty

  (<+>) x y = x `hardcat` space `hardcat` spaces `hardcat` y

  line = E fline
  linebreak = E flinebreak

  align = E . falign . unE
  nest k = E . fnest k . unE
  group = E . fgroup . unE

-- Pretty printing interpretation of FliPprD for convenience, it is a sort of
-- unembedding but we use untyped variants.

newtype RName = RName Int deriving newtype (Num, Show, Enum)

newtype IName = IName Int deriving newtype (Num, Show, Enum)

-- newtype Defs.PprExp (a :: FType) = Defs.PprExp {Defs.pprExp :: Prec -> State (RName, IName) D.Doc}

{-# WARNING VarMFliPpr "to be removed" #-}
newtype VarMFliPpr a = VarMFliPpr {runVarMFliPpr :: State (RName, IName) a}
  deriving newtype (Functor, Applicative, Monad, MonadState (RName, IName))

instance Defs.VarM VarMFliPpr where
  newVar = do
    rn <- newRName
    return $ "f" ++ show rn
  nestScope = id

newIName :: VarMFliPpr IName
newIName = do
  (i, v) <- get
  let !v' = v + 1
  put (i, v')
  return v

newRName :: VarMFliPpr RName
newRName = do
  (i, v) <- get
  let !i' = i + 1
  put (i', v)
  return i

pprIName :: IName -> D.Doc ann
pprIName n
  | coerce n < length fancyNames = fromString [fancyNames !! coerce n]
  | otherwise = fromString ("x" ++ show n)
  where
    fancyNames = "xyzwsturabcdeijklmnpqv"

type PrinterI ann = Defs.Norm (Defs.PprExp VarMFliPpr ann :: FType -> Type)

instance FliPprE (Const IName) (PrinterI ann) where
  fapp e1 e2 = Defs.PprExpN $ \k -> do
    d1 <- Defs.pprExpN e1 9
    let d2 = pprIName (getConst e2)
    return $ applyWhen (k > 9) D.parens $ d1 D.<+> d2

  farg h = Defs.PprExpN $ \k -> do
    x <- newIName
    d <- Defs.pprExpN (h $ Const x) 0
    return $
      applyWhen (k > 0) D.parens $
        D.fillSep [fromString "\\" <> pprIName x D.<+> fromString "->", d]

  fcharAs a cs = Defs.PprExpN $ \k -> do
    let da = pprIName $ getConst a
    return $ applyWhen (k > 9) D.parens $ da D.<+> fromString "`charAs`" D.<+> fromString (show cs)

  fcase a bs = Defs.PprExpN $ \k -> do
    let da = pprIName $ getConst a
    ds <- forM bs $ \(Branch (PartialBij s _ _) f) -> do
      x <- newIName
      df <- Defs.pprExpN (f $ Const x) 0
      return $ D.group $ D.nest 2 $ fromString s D.<+> fromString "$" D.<+> fromString "\\" <> pprIName x D.<+> fromString "->" D.<+> df
    return $
      applyWhen (k > 9) D.parens $
        D.group $
          fromString "case_"
            D.<+> da
            D.<+> fromString "["
            <> D.align (D.concatWith (\x y -> D.fillSep [x <> fromString ",", y]) ds <> fromString "]")

  funpair a f = Defs.PprExpN $ \k -> do
    let da = pprIName (getConst a)
    x <- newIName
    y <- newIName
    db <- Defs.pprExpN (f (Const x) (Const y)) 0
    return $
      applyWhen (k > 0) D.parens $
        D.align $
          D.group $
            D.fillSep
              [ fromString "let" D.<+> D.parens (pprIName x <> fromString "," D.<+> pprIName y) D.<+> fromString "=" D.<+> D.align da
              , fromString "in" D.<+> D.align db
              ]

  fununit a e = Defs.PprExpN $ \k -> do
    let da = pprIName (getConst a)
    de <- Defs.pprExpN e 0
    return $
      applyWhen (k > 0) D.parens $
        D.align $
          D.group $
            D.fillSep
              [ fromString "let () =" D.<+> D.align da
              , fromString "in" D.<+> D.align de
              ]

  ftext s = Defs.PprExpN $ \k ->
    return $ applyWhen (k > 9) D.parens $ fromString "text" D.<+> fromString (show s)

  fcat a b = Defs.PprExpN $ \k -> do
    da <- Defs.pprExpN a 5
    db <- Defs.pprExpN b 5
    return $ applyWhen (k > 5) D.parens $ D.group $ D.fillSep [da, fromString "<#>" D.<+> db]

  fbchoice a b = Defs.PprExpN $ \k -> do
    da <- Defs.pprExpN a 4
    db <- Defs.pprExpN b 4
    return $ applyWhen (k > 4) D.parens $ D.group $ D.fillSep [da, fromString "<?" D.<+> db]

  fempty = Defs.PprExpN $ const $ return $ fromString "empty"
  fline = Defs.PprExpN $ const $ return $ fromString "line"
  flinebreak = Defs.PprExpN $ const $ return $ fromString "linebreak"

  fspace = Defs.PprExpN $ const $ return $ fromString "space"
  fspaces = Defs.PprExpN $ const $ return $ fromString "spaces"

  fline' = Defs.PprExpN $ const $ return $ fromString "line'"
  fnespaces' = Defs.PprExpN $ const $ return $ fromString "nespaces'"

  fgroup a = Defs.PprExpN $ \k -> do
    da <- Defs.pprExpN a 10
    return $ applyWhen (k > 9) D.parens $ fromString "group" D.<+> da

  falign a = Defs.PprExpN $ \k -> do
    da <- Defs.pprExpN a 10
    return $ applyWhen (k > 9) D.parens $ fromString "align" D.<+> da

  fnest n a = Defs.PprExpN $ \k -> do
    da <- Defs.pprExpN a 10
    return $ applyWhen (k > 9) D.parens $ fromString "nest" D.<+> D.pretty n D.<+> da

instance D.Pretty (FliPpr t) where
  pretty (FliPpr m) = evalState (runVarMFliPpr $ Defs.pprExpN m 0) (0, 0)