{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- | A type class for mutually recursive definitions in finally-tagless DSLs.
--
-- = Motivation
--
-- When we implement DSLs, we sometimes do not want to use Haskell level
-- recursions to represent recursions in a guest language. An example is
-- context-free grammars, where recursive definitions should result in
-- observable cycles so that we can use parsing algorithms. Similarly, we want
-- to construct a graph.
--
-- Having a function corresponds to @letrec@ seems not difficult. For example,
-- given an expression type constructor @f@, we can easily give methods to
-- define n-recursive definitions for each n.
--
-- > letrec1 :: (f a -> f a) -> (f a -> f r) -> f r
-- > letrec2 :: ((f a, f b) -> (f a, f b)) -> ((f a, f b) -> f r) -> f r
-- > letrec3 :: ((f a, f b, f c) -> (f a, f b, c)) -> ((f a, f b, f c) -> f r) -> f r
--
-- This suggests the following general interface
--
-- > letrecN :: HList Proxy as -> (HList f as -> HList f as) -> (HList f as -> f r) -> f r
--
-- Here, @HList f [a1,...,an]@ is isomorphic to @(f a1, ..., f an)@.
--
-- However, in this representation, we need to be careful for @as@, i.e., the
-- types of recursively defined functions. Also, we need to pattern match whole
-- @HList f as@ at first or use de Bruijn indices to refer to
-- recursively-defined variables. As a result, this representation makes it
-- tedious to define recursive definitions step-by-step or add recursively-defined
-- variables.
--
-- For example of grammar-description DSL, we want to define copies on
-- non-terminals for different precedence level to control over where parentheses
-- are allowed. So, we want to convert
--
-- > letrecWithPrec ::
-- >    Prec -- maximum precedence
-- >    -> ((Prec -> f a) -> (Prec -> f a))
-- >    -> ((Prec -> f a) -> f r)
-- >    -> f r
--
-- into @letrecN@. Notice that this function takes the maximum precedence level in the first
-- argument as we do not want to produce recursive definitions for each @Prec@, as @Prec@ is
-- typicall a synonym for an integer type such @Int@. However, this dynamic nature makes it
-- far from trivial to use @letrecN@ as we need to specify @as@ statically; we might address
-- this by using existential types, but it would require nontrivial programming.
--
-- = What This Module Provides
--
-- This module is designed to address the issue, allowing us to define recursive definitions
-- step-by-step. The basic interface is 'letr1' and 'local'.
--
-- > letr1 :: (Defs f) => (f a -> DefM f (f a, r)) -> DefM f r
-- > local :: (Defs f) => DefM f (f t) -> f t
--
-- By this function, one can easily define the above mentioned function as below:
--
-- > letrsP :: (Defs f) => Prec -> ((Prec -> f a) -> DefM f (Prec -> f a, r)) -> DefM f r
-- > letrsP 0 h = snd <$> h (const $ error "letrsP: out of bounds")
-- > letrsP k h = letr $ \fk -> letrs (k - 1) $ \f -> do
-- >  (f', r) <- h $ \x -> if x == k then fk else f x
-- > return (f', (f' k, r))
-- >
-- > letrecWithPrec maxPrec h hr = local $ letrsP maxPrec (\f -> pure (h f, hr f))
--
-- All you have to do is to make your expression type an instance of 'Defs'.
--
-- = Limitation
--
-- Similar to the limitation of (parametric variants of) HOAS compared with the
-- de Bruijn representation, this representation is not good at supporting
-- semantics that refers to the whole recursive definitions. A remedy is to convert
-- the representation to de Bruijn representations or others, e.g., by using Atkey's
-- unembedding or similar.
module Defs (
  -- * High-level I/F
  Defs (..),
  DefM (..),
  share,
  share1,
  local,
  def,
  mfixDefM,
  Tip (..),
  RecM (..),
  RecArg (..),
  FromBounded (..),

  -- * letrec
  letrec,
  letrecM,
  letrec',

  -- * Helper functions for defining 'Alternative' instances
  manyD,
  someD,

  -- * Low-level primitives
  letr1,
  letrs,

  -- * Normalized form
  NDefs (..),
  HList (..),
  Norm (..),

  -- * Pretty-printing
  VarM (..),
  PprExp (..),
  pattern PprExpN,
  pprExpN,
)
where

import Control.Applicative (Alternative (..))
import Control.Monad.Trans.Reader (ReaderT (..))
import qualified Control.Monad.Trans.State.Lazy as LState (StateT (..))
import qualified Control.Monad.Trans.State.Strict as SState (StateT (..))
import qualified Control.Monad.Trans.Writer.Lazy as LWriter
import qualified Control.Monad.Trans.Writer.Strict as SWriter
import Data.Coerce (coerce)
import qualified Data.Fin as F
import Data.Functor.Compose
import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))
import Data.Int (Int8)
import Data.Kind (Type)
import Data.Proxy
import Data.String (IsString (..))
import qualified Data.Type.Nat as F
import Data.Word (Word8)
import Internal.THUtil
import Prettyprinter as D

-- | A class to control looping structure. The methods are not supposed to be used directly, but via derived forms.
--
-- @let rec x1 = e1 and x2 = e2 in e@ is represented by:
--
-- @
-- unliftD $ letrD $ \x1 -> letrD $ \x2 ->
--   consD e2 $ consD e1 $ liftD e
-- @
--
-- prop> unliftD (liftD e) == e
-- prop> consD e (letrD $ \x -> consD ex r) == letrD $ \x -> consD ex (consD e r)
class Defs (f :: k -> Type) where
  -- By kztk @ 2020-11-26
  -- We will use the following methods for recursive definitions
  -- By kztk @ 2021-02-17
  -- Use the standard lists instead of special datatypes.

  -- | @D f [a1,...,an] a@ can be understood as triples of:
  --
  --   * a product of @a1,...,an@ (called pending list), which may refer to y1 ... ym below
  --   * (implicit) recursive definitions already constructed (y1 = e1,...,ym = em)
  --   * @e :: f a@ of @let rec ... in e@
  data D f :: [k] -> k -> Type

  -- | Constructs an empty recursive definition such as @let rec in e@.
  liftD :: f a -> D f '[] a

  -- | Produces recursive definition
  unliftD :: D f '[] a -> f a

  -- | Adds an expression to the pending list
  consD :: f a -> D f as r -> D f (a ': as) r

  -- | Closes the head expression in the pending list to move it to the already
  -- constructed recursive definitions.
  --
  -- This method inspired by the trace operator in category theory (it is named
  -- after "let rec" and "trace").
  letrD :: (f a -> D f (a : as) r) -> D f as r

letrec' :: (Defs f) => HList (Compose ((->) (HList f as)) f) as -> (HList f as -> f r) -> f r
letrec' hs0 hr0 = local (snd <$> go id hs0 hr0)
  where
    go ::
      (Defs f) =>
      (HList f as -> HList f as0)
      -> HList (Compose ((->) (HList f as0)) f) as
      -> (HList f as -> f r)
      -> DefM f (HList f as, f r)
    go _ HNil hr = pure (HNil, hr HNil)
    go p (HCons h hs) hr = do
      letr1 $ \x -> do
        (xs, r) <- go (p . HCons x) hs (hr . HCons x)
        pure (getCompose h (p $ HCons x xs), (HCons x xs, r))

letrec :: (Defs f) => HList Proxy as -> (HList f as -> (HList f as, f r)) -> f r
letrec sh h = local $ letrecM sh (pure . h)

letrecM :: (Defs f) => HList Proxy as -> (HList f as -> DefM f (HList f as, res)) -> DefM f res
letrecM HNil h = snd <$> h HNil
letrecM (HCons _ sh) h =
  letr1 $ \x -> letrecM sh $ \xs -> do
    (vvs, r) <- h (HCons x xs)
    case vvs of
      HCons v vs -> pure (vs, (v, r))

data HList f as where
  HNil :: HList f '[]
  HCons :: f a -> HList f as -> HList f (a ': as)

newtype Norm e a = Norm {unNorm :: e a}

-- | Normalized form of 'Defs', which effectively disallows @consD e (letrD h)@
class NDefs (f :: k -> Type) where
  data ND f :: [k] -> k -> Type

  defN :: HList f as -> f a -> ND f as a
  localN :: ND f '[] a -> f a
  letrN :: (f a -> ND f (a : as) r) -> ND f as r

-- Normalization
instance (NDefs f) => Defs (Norm f) where
  newtype D (Norm f) as a = FromND {fromND :: forall bs. (HList f as -> HList f bs) -> ND f bs a}

  liftD e = FromND $ \k -> defN (k HNil) (unNorm e)
  unliftD d = Norm $ localN $ fromND d id
  consD e d = FromND $ \k -> fromND d (k . HCons (unNorm e))
  letrD h = FromND $ \k -> letrN $ \a -> fromND (h $ Norm a) $ \(HCons ex r) -> HCons ex (k r)

-- | A monad to give better programming I/F.
--   We intentionally did not make it an instance of 'MonadFix'.
newtype DefM f a = DefM {unDefM :: forall as r. (a -> D f as r) -> D f as r}

instance Functor (DefM exp) where
  fmap f m = DefM $ \k -> unDefM m (k . f)
  {-# INLINE fmap #-}

instance Applicative (DefM exp) where
  pure a = DefM $ \k -> k a
  {-# INLINE pure #-}

  a <*> b = DefM $ \k -> unDefM a $ \av -> unDefM b $ \bv -> k (av bv)
  {-# INLINE (<*>) #-}

instance Monad (DefM exp) where
  return = pure
  {-# INLINE return #-}

  m >>= f = DefM $ \k -> unDefM m $ \v -> unDefM (f v) k
  {-# INLINE (>>=) #-}

-- | A basic building block for mutual recursion.
--
--  To define a recursion, simply use this function.
--
--  > letr1 $ \f ->
--  >   def fdef $
--  >   ... f ...
--
--  To define mutual recursions, nest this function.
--
-- > letr1 $ \f -> letr1 $ \g ->
-- >   def fdef >>>
-- >   def gdef $
-- >   ... f ... g ...
letr1 :: (Defs f) => (f a -> DefM f (f a, r)) -> DefM f r
letr1 h = DefM $ \k -> letrD $ \a -> unDefM (h a) $ \(b, r) -> consD b (k r)

-- | A variant of 'many' defined without Haskell-level recursion.
manyD :: (Defs f, Alternative f) => f a -> f [a]
manyD d = local $ letr1 $ \a -> return (pure [] <|> (:) <$> d <*> a, a)

-- | A variant of 'some' defined without Haskell-level recursion.
someD :: (Defs f, Alternative f) => f a -> f [a]
someD d = local $ letr1 $ \m -> letr1 $ \s ->
  def ((:) <$> d <*> m) $
    def (pure [] <|> s) $
      return s

-- | 'share's computation.
share :: (RecM a m) => a -> m a
share s =
  -- letrec x = e in x where x doesn't belong to fv(e)
  letr $ \x -> pure (s, x)

share1 :: (Defs f) => f a -> DefM f (f a)
share1 s =
  letr1 $ \x -> pure (s, x)

-- | Makes definions to be 'local'.
--
-- For example, in the follownig code, the scope of shared computation is limited to @foo@; so using @foo@ twice copies @defa@.
--
-- > foo = local $ do
-- >    a <- share defa
-- >     ...
local :: (Defs f) => DefM f (f t) -> f t
local m = unliftD $ unDefM m liftD

-- | @def a@ is a synonym for @fmap (a,)@, which is convenient to be used with 'letr'.
def :: (Functor f) => a -> f b -> f (a, b)
def a = fmap (a,)
{-# INLINE def #-}

-- | A class that provides a generalized version 'letr' of 'letr1'
--
-- One can think this as an argument resticted version of 'mfix'. See
-- 'mfixDefM'. 'letr' provides a building block for various @a@ and @m@
-- of @(a -> m a) -> m a@. Instances of this typeclass are responsible for
-- the @m@ part. For the @a@ part, 'RecArg' is responsible via the instance
-- @(RecArg f t) => RecM t (DefM f)@.
class (Monad m) => RecM t m where
  letr :: (t -> m (t, r)) -> m r

instance (RecArg f t) => RecM t (DefM f) where
  letr = letrDefM

instance (RecM t m) => RecM t (LState.StateT s m) where
  letr f = LState.StateT $ \state -> do
    letr $ \a -> do
      ((a', r), state') <- LState.runStateT (f a) state
      pure (a', (r, state'))

instance (RecM t m) => RecM t (SState.StateT s m) where
  letr f = SState.StateT $ \state -> do
    letr $ \a -> do
      ((a', r), state') <- SState.runStateT (f a) state
      pure (a', (r, state'))

instance (RecM t m) => RecM t (ReaderT s m) where
  letr f = ReaderT $ \state -> letr $ \a -> runReaderT (f a) state

instance (RecM t m, Monoid w) => RecM t (LWriter.WriterT w m) where
  letr f = LWriter.WriterT $ do
    letr $ \a -> do
      ((a', r), w) <- LWriter.runWriterT (f a)
      pure (a', (r, w))

instance (RecM t m, Monoid w) => RecM t (SWriter.WriterT w m) where
  letr f = SWriter.WriterT $ do
    letr $ \a -> do
      ((a', r), w) <- SWriter.runWriterT (f a)
      pure (a', (r, w))

-- | A class to define what kind of @a@ for which we can define
-- @letr :: (a -> m a) -> m a@. This typeclass focuses on the
-- case where @m ~ DefM f@ because other cases are handled by
-- 'RecM'. Very roughly speaking, @a@ must be a product-like
-- datatype of types of the form of @f ai@ for some @ai@.
--
-- Due the restriction of Haskell's type inference, this module
-- does not provide an instance @RecArg f (f a)@, which should
-- serve as the base case of instance declarations. Instead, this
-- module provides an instance @RecArg f (Identity (f a))@. Thus,
-- in practice, an user needs to define an instance for the user's
-- own expression type @F@ by using @DerivingVia@, as:
--
-- > deriving via Identity (F a) instance RecArg F (F a)
class RecArg f t where
  letrDefM :: (t -> DefM f (t, r)) -> DefM f r

-- | A variant of 'mfix'. This function is supported to be used as:

--- > {-# LANGUAGE RecursiveDo, RebindableSyntax #-}
--  >
--  > someFunc = do
--  >     rec a <- share $ ... a ... b ...
--  >         b <- share $ ... a ... b ...
--  >     ...
--  >   where mfix = mfixDefM
mfixDefM :: (RecM a m) => (a -> m a) -> m a
mfixDefM f = letr $ \a -> (,a) <$> f a

instance RecArg f () where
  letrDefM f = snd <$> f ()

newtype Tip a = Tip {unTip :: a}

instance (Defs f) => RecArg f (Tip (f a)) where
  letrDefM :: forall r. (Tip (f a) -> DefM f (Tip (f a), r)) -> DefM f r
  letrDefM = coerce (letr1 :: (f a -> DefM f (f a, r)) -> DefM f r)
instance (Defs f) => RecArg f (Identity (f a)) where
  letrDefM :: forall r. (Identity (f a) -> DefM f (Identity (f a), r)) -> DefM f r
  letrDefM = coerce (letr1 :: (f a -> DefM f (f a, r)) -> DefM f r)

instance (RecArg f a, RecArg f b) => RecArg f (a, b) where
  letrDefM f = letrDefM $ \b -> letrDefM $ \a -> do
    ((a', b'), r) <- f (a, b)
    return (a', (b', r))
instance (RecArg m a, RecArg m b, RecArg m c) => RecArg m (a, b, c) where
  letrDefM f = letrDefM $ \c -> letrDefM $ \b -> letrDefM $ \a -> do
    ((a', b', c'), r) <- f (a, b, c)
    return (a', (b', (c', r)))

instance (RecArg m a, RecArg m b, RecArg m c, RecArg m d) => RecArg m (a, b, c, d) where
  letrDefM f = letrDefM $ \ ~(c, d) -> letrDefM $ \ ~(a, b) -> do
    ((a', b', c', d'), r) <- f (a, b, c, d)
    return ((a', b'), ((c', d'), r))

-- Use template haskell to generate instances for n-tuples
$(concat <$> sequence [genTupleArgDecl i [t|RecArg|] | i <- [5 .. 32]])

instance RecArg f (HList g '[]) where
  letrDefM f = do
    (_, r) <- f HNil
    pure r

instance
  (RecArg f a, RecArg f (HList Identity as)) =>
  RecArg f (HList Identity (a : as))
  where
  letrDefM f = letrDefM $ \a -> letrDefM $ \as -> do
    (res, r) <- f (HCons (Identity a) as)
    case res of
      HCons (Identity v) vs ->
        pure (vs, (v, r))

-- | @letrs [k1,...,kn] $ \f -> (def fdef r)@ to mean
--
-- > letr $ \f1 -> letr $ \f2 -> ... letr $ \fn ->
-- >   def (fdef k1) >>> ... >>> def (fdef kn) $ do
-- >   let f k = fromJust $ lookup k [(k1,f1), ..., (kn,fn)]
-- >   r
letrs :: (Eq k, RecM a f) => [k] -> ((k -> a) -> f (k -> a, r)) -> f r
letrs [] h = snd <$> h (const $ error "Defs.letrs: out of bounds")
letrs (k : ks) h = letr $ \fk -> letrs ks $ \f -> do
  (f', r) <- h $ \x -> if x == k then fk else f x
  return (f', (f' k, r))

-- | A newtype wrapper for Bounded types. A typical use is an instance declaration such as:
--
-- > deriving via (FromBounded YourType -> a) instance (RecArg f a) => RecArg f (YourType -> a)
newtype FromBounded b = FromBounded {getBounded :: b}
  deriving newtype (Eq, Ord, Enum, Bounded, Num, Real, Integral, Show)

letrsB ::
  (Eq b, Enum b, Bounded b, RecM a m) =>
  ((b -> a) -> m (b -> a, r))
  -> m r
-- FIXME: we should consider using binary search
letrsB = letrs [minBound .. maxBound]

instance (Eq b, Enum b, Bounded b, RecArg f a) => RecArg f (FromBounded b -> a) where
  letrDefM = letrsB

-- Instances of RecArg (b -> a) for concrete bounded types b.

deriving via (FromBounded Bool -> a) instance (RecArg f a) => RecArg f (Bool -> a)
deriving via (FromBounded Word8 -> a) instance (RecArg f a) => RecArg f (Word8 -> a)
deriving via (FromBounded Int8 -> a) instance (RecArg f a) => RecArg f (Int8 -> a)
deriving via (FromBounded () -> a) instance (RecArg f a) => RecArg f (() -> a)
deriving via (FromBounded (F.Fin n) -> a) instance (RecArg f a, F.SNatI k, F.S k ~ n) => RecArg f (F.Fin n -> a)

deriving via (b -> a) instance (RecArg f (b -> a)) => RecArg f (Identity b -> a)
deriving via (b -> a) instance (RecArg f (b -> a)) => RecArg f (Const b x -> a)

{-# WARNING VarM "This class will be removed soon. Use 'EbU' library for pretty-printing" #-}

-- | Monads for managing variable names
class (Monad m) => VarM m where
  -- | A new variable name, which may or may not differ in calls.
  --   For de Bruijn levels, use the Reader monad and define
  --
  --   >  newVar = do {i <- ask ; return ("x" ++ show i ) }
  --
  --   Just for using different names, use the State monad and define
  --
  --   >  newVar = do { i <- get ; put (i + 1) ; return ("x" ++ show i) }
  --
  --   This representation does not cover de Bruijn indices; we do not support them.
  newVar :: m String

  -- | +1 to the nesting level. This is just identity if ones to assign different names for different variables.
  nestScope :: m a -> m a

type Precedence = Int

-- | A general pretty-printer for 'Defs' methods. Use different @m@ printing different HOAS, to avoid overlapping instance.
{-# WARNING PprExp "To be removed" #-}

newtype PprExp m ann _a = PprExp {pprExp :: Precedence -> m (D.Doc ann)}

pattern PprExpN :: (Precedence -> m (D.Doc ann)) -> Norm (PprExp m ann) a
pattern PprExpN a = Norm (PprExp a)

pprExpN :: Norm (PprExp m ann) a -> Precedence -> m (D.Doc ann)
pprExpN = pprExp . unNorm

instance (VarM m) => NDefs (PprExp m ann) where
  newtype ND (PprExp m ann) _as _a = PDefs {pdefs :: [String] -> Precedence -> m (D.Doc ann)}

  defN exps r = PDefs $ \xs k -> do
    bs <- D.vcat <$> go xs exps
    dr <- pprExp r 0

    pure $
      parensIf (k > 0) $
        D.align $
          D.vcat
            [ "let" D.<+> D.align bs
            , "in" D.<+> dr
            ]
    where
      parensIf b = if b then D.parens else id
      go :: [String] -> HList (PprExp m ann) as -> m [D.Doc ann]
      go _ HNil = pure []
      go (x : xs) (HCons e es) = do
        de <- pprExp e 0
        res <- go xs es
        pure $ (fromString x D.<+> "=" D.<+> D.align de) : res
      go _ _ = error "Unreachable"

  localN d = PprExp $ \k ->
    pdefs d [] k
  letrN h = PDefs $ \xs k -> do
    x <- newVar
    nestScope $ pdefs (h (PprExp $ \_ -> pure $ fromString x)) (x : xs) k
