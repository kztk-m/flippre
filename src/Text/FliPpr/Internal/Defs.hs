{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Text.FliPpr.Internal.Defs
  ( -- * Definitions
    DType (..),
    DTypeVal (..),
    Defs (..),
    DefM (..),
    type (<*),
    type Lift,
    Tip(..),

    -- * Helper functions for defining 'Alternative' instances
    manyD,
    someD,

    -- -- * 'DType'-indexed functions
    -- DefType (..),

    -- ** High-level I/F
    share,
    local,
    def,
    mfixDefM,
    LetArg(..),

    -- ** Low-level primitives
    letr, letrs,

    -- * Mapping functios
    TransD,

    -- * Pretty-printing
    VarM (..),
    PprDefs (..),
  )
where

import           Data.Functor.Identity (Identity (..))

import           Control.Applicative   (Alternative (..))
import qualified Data.Fin              as F
import           Data.Int              (Int8)
import           Data.Kind             (Type)
import qualified Data.Type.Nat         as F
import           Data.Word             (Word8)
import qualified Text.FliPpr.Doc       as D

import           Data.Coerce           (coerce)
import           Data.Functor.Const    (Const)

-- | A type for (mutually recursive) definitions
data DType k
  = -- | Type lifted from @ft@
    T k
  | -- | Expressions that may share some definitions
    k :<*: DType k

type a <* b = a ':<*: b

type Lift a = 'T a

infixr 4 <*

infixr 4 :<*:

-- | Nested products of @f@ types.
--
--   The argument of 'VT' and the first argument of 'VCons' are intensionally lazy, as
--   we may want to use Haskell's recursive definitions to implement 'letrDS'.

data DTypeVal (f :: k -> Type) :: DType k -> Type where
  VT ::    f ft -> DTypeVal f (Lift ft)
  VCons :: f a -> !(DTypeVal f b) -> DTypeVal f (a <* b)

-- | A class to control looping structure. The methods are not supposed to be used directly, but via derived forms.
class Defs (f :: k -> Type) where
  -- | Interpretation of product types. We are expecting that
  -- @Fs f a@ is isomorphic to @forall r. (DTypeVal f a -> f r) -> f r@,
  -- but having direct interpretation would be convenient, at least to define 'letrDS'.
  data Fs f :: DType k -> Type
  -- DS stands for "direct style".

  -- By kztk @ 2020-11-26
  -- We will use the following methods for recursive definitions
  liftDS :: f a -> Fs f ( 'T a)
  unliftDS :: Fs f ( 'T a) -> f a

  consDS :: f a -> Fs f b -> Fs f (a <* b)

  -- | A method inspired by the trace operator in category theory (it is named
  -- after "let rec" and "trace"), a basic building block of mutual recursions.
  letrDS :: (f a -> Fs f (a <* r)) -> Fs f r

-- | A monad to give better programming I/F. This actually is a specialized version of a codensity monad: @Def f@ is @Codensity (Fs f)@.
--   We intentionally did not make it an instance of 'MonadFix'.
newtype DefM f a = DefM {unDefM :: forall r. (a -> Fs f r) -> Fs f r}

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
--  > letr $ \f ->
--  >   def fdef $
--  >   ... f ...
--
--  To define mutual recursions, nest this function.
--
-- > letr $ \f -> letr $ \g ->
-- >   def fdef >>>
-- >   def gdef $
-- >   ... f ... g ...
letr :: Defs f => (f a -> DefM f (f a, r)) -> DefM f r
letr h = DefM $ \k -> letrDS $ \a -> unDefM (h a) $ \(b, r) -> consDS b (k r)

-- | @letrs [k1,...,kn] $ \f -> (def fdef r)@ to mean
--
-- > letr $ \f1 -> letr $ \f2 -> ... letr $ \fn ->
-- >   def (fdef k1) >>> ... >>> def (fdef kn) $ do
-- >   let f k = fromJust $ lookup k [(k1,f1), ..., (kn,fn)]
-- >   r
letrs :: (Defs f, Eq k) => [k] -> ((k -> f a) -> DefM f (k -> f a, r)) -> DefM f r
letrs [] h = snd <$> h (const $ error "Text.FliPpr.Internal.Defs.letrs: out of bounds")
letrs (k:ks) h = letr $ \fk -> letrs ks $ \h' -> do
  (dh'', r) <- h $ \x -> if x == k then fk else h' x
  return (dh'', (dh'' k, r))

-- | A variant of 'many' defined without Haskell-level recursion.
manyD :: (Defs f, Alternative f) => f a -> f [a]
manyD d = local $ letr $ \a -> return (pure [] <|> (:) <$> d <*> a, a)

-- | A variant of 'some' defined without Haskell-level recursion.
someD :: (Defs f, Alternative f) => f a -> f [a]
someD d = local $ letr $ \m -> letr $ \s ->
   def ((:) <$> d <*> m) $
   def (pure [] <|> s) $
   return s

-- | @def a@ is a synonym of @fmap (a,)@, which is convenient to be used with 'letr'.
def :: Functor f => a -> f b -> f (a, b)
def a = fmap (a,)
{-# INLINE def #-}

-- | @TransD f a@ maps @f@ to leaves in @a@. For example, @TransD f (Lift a ** Lift b) = (Lift (f a) ** Lift (f b))@.
type family TransD f a = b | b -> a f where
  TransD f ( 'T a) = 'T (f a)
  TransD f (a <* b) = f a <* TransD f b

-- -- | To perform induction on the structure of @DType k@.
-- class DefType (r :: DType k) where
--   indDType ::
--     forall f.
--     (forall a. f ( 'T a)) ->
--     (forall a b. (DefType a, DefType b) => f (a <* b)) ->
--     f r

-- instance DefType ( 'T a) where
--   indDType f _ = f

-- instance (DefType a, DefType b) => DefType (a <* b) where
--   indDType _ step = step

-- newtype LetG f a = LetG (forall r. (DTypeVal f a -> DefM f (DTypeVal f a,r)) -> DefM f r)

-- letrG :: (Defs f, DefType a) => (DTypeVal f a -> DefM f (DTypeVal f a, r)) -> DefM f r
-- letrG = let LetG f = indDType letrG1 letrGStep in f
--   where
--     letrG1 :: Defs f => LetG f ('T t)
--     letrG1 = LetG $ \h -> letr $ \x -> h (VT x) >>= \case { (VT a, r) -> return (a, r) }

--     letrGStep :: (DefType a, DefType b, Defs f) => LetG f (a ** b)
--     letrGStep = LetG $ \h -> letrG $ \b -> letrG $ \a -> arr <$> h (VCons a b)

--     arr :: (DTypeVal f (a ** b), r) -> (DTypeVal f a, (DTypeVal f b, r))
--     arr (VCons a b, r) = (a, (b, r))

-- | A class that provides a generalized version of 'letr'.
class Defs f => LetArg f t where
  letrGen :: (t -> DefM f (t, r)) -> DefM f r

instance Defs f => LetArg f () where
  letrGen f = snd <$> f ()


newtype Tip a = Tip { unTip :: a }

instance Defs f => LetArg f (Tip (f a)) where
  letrGen :: forall r. (Tip (f a) -> DefM f (Tip (f a), r)) -> DefM f r
  letrGen f = letr (coerce f :: f a -> DefM f (f a, r))

instance (LetArg f a, LetArg f b) => LetArg f (a, b) where
  letrGen f = letrGen $ \b -> letrGen $ \a -> do
                ((a', b'), r) <- f (a, b)
                return (a', (b', r))

instance (LetArg f a, LetArg f b, LetArg f c) => LetArg f (a, b, c) where
  letrGen f = letrGen $ \c -> letrGen $ \b -> letrGen $ \a -> do
    ((a', b', c'), r) <- f (a, b, c)
    return (a', (b', (c', r)))

instance (LetArg f a, LetArg f b, LetArg f c, LetArg f d) => LetArg f (a, b, c, d) where
  letrGen f = letrGen $ \ ~(c,d) -> letrGen $ \ ~(a,b) -> do
    ((a', b', c', d'), r) <- f (a, b, c, d)
    return ( (a', b'), ( (c', d'), r ) )

instance (LetArg f a1, LetArg f a2, LetArg f a3, LetArg f a4, LetArg f a5) => LetArg f (a1, a2, a3, a4, a5) where
  letrGen f = letrGen $ \ ~(a4,a5) -> letrGen $ \ ~(a1, a2, a3) -> do
    ((b1, b2, b3, b4, b5), r) <- f (a1, a2, a3, a4, a5)
    return ( (b1, b2, b3), ( (b4, b5), r ) )

instance (LetArg f a1, LetArg f a2, LetArg f a3, LetArg f a4, LetArg f a5, LetArg f a6) => LetArg f (a1, a2, a3, a4, a5, a6) where
  letrGen f = letrGen $ \ ~(a4,a5, a6) -> letrGen $ \ ~(a1, a2, a3) -> do
    ((b1, b2, b3, b4, b5, b6), r) <- f (a1, a2, a3, a4, a5, a6)
    return ( (b1, b2, b3), ( (b4, b5, b6), r ) )


newtype FromBounded b = FromBounded { getBounded :: b } deriving (Eq, Ord, Enum, Bounded, Num, Real, Integral, Show)

letrsB :: (Eq b, Enum b, Bounded b, LetArg f a) =>
          ((b -> a) -> DefM f (b -> a, r)) -> DefM f r
letrsB = go minBound
  where
    go :: (Eq b, Enum b, Bounded b, LetArg f a) =>
          b -> ((b -> a) -> DefM f (b -> a, r)) -> DefM f r
    go b h
      | b == maxBound =
        letrGen $ \fb -> do
          (f', r) <- h $ const fb
          return (f' maxBound, r)
      | otherwise =
        letrGen $ \fb -> go (succ b) $ \f -> do
          (f', r) <- h $ \x -> if x == b then fb else f x
          return (f', (f' b, r))

instance (Eq b, Enum b, Bounded b, LetArg f a) => LetArg f (FromBounded b -> a) where
  letrGen = letrsB

-- Instances of concrete bounded types: we don't make instances like LetArg f (Int -> a),
-- as they are unrealistic.

instance LetArg f a => LetArg f (Bool -> a) where
  letrGen = letrsB

instance (LetArg f a, F.SNatI m, 'F.S m ~ n) => LetArg f (F.Fin n -> a) where
  letrGen = letrsB

instance LetArg f a => LetArg f (Word8 -> a) where
  letrGen = letrsB

instance LetArg f a => LetArg f (Int8 -> a) where
  letrGen = letrsB

instance LetArg f a => LetArg f (() -> a) where
  letrGen = letrsB

instance LetArg f (b -> a)  => LetArg f (Identity b -> a) where
  letrGen :: forall r. ((Identity b -> a) -> DefM f (Identity b -> a, r)) -> DefM f r
  letrGen h = letrGen (coerce h :: (Identity b -> a) -> DefM f (Identity b -> a, r))

instance LetArg f (b -> a) => LetArg f (Const b x -> a) where
  letrGen :: forall r. ((Const b x -> a) -> DefM f (Const b x -> a, r)) -> DefM f r
  letrGen h = letrGen (coerce h :: (Const b x -> a) -> DefM f (Const b x -> a , r))

-- newtype LetArgFin f a n = LetArgFin { runLetArgFin :: LetArg f a => forall r. ( (F.Fin n -> a) -> DefM f (F.Fin n -> a, r)) -> DefM f r }

-- instance (LetArg f a, F.SNatI n) => LetArg f (F.Fin n -> a) where
--   letrGen = runLetArgFin $ F.induction f0 fstep
--     where
--       f0 = LetArgFin $ \f -> snd <$> f (const $ error "letrGen: no inhabitants in Fin Z")
--       fstep p = LetArgFin $ \h ->
--         letrGen $ \h0 -> runLetArgFin p $ \hstep -> do
--           (h', r) <- h $ \case { F.FZ -> h0 ; F.FS n -> hstep n }
--           return (h' . F.FS, (h' F.FZ , r))

-- | A variant of 'mfix'. This function is supported to be used as:
--
--- > {-# LANGUAGE RecursiveDo, RebindableSyntax #-}
--  >
--  > someFunc = do
--  >     rec a <- share $ ... a ... b ...
--  >         b <- share $ ... a ... b ...
--  >     ...
--  >   where mfix = mfixDefM
mfixDefM :: (Defs f, LetArg f a) => (a -> DefM f a) -> DefM f a
mfixDefM f = letrGen $ \a -> (,a) <$> f a

-- | 'share's computation.
share :: Defs f => f a -> DefM f (f a)
share s = DefM $ \k -> letrDS $ \a -> consDS s (k a)

-- | Makes definions to be 'local'.
--
-- For example, in the follownig code, the scope of shared computation is limited to @foo@; so using @foo@ twice copies @defa@.
--
-- > foo = local $ do
-- >    a <- share defa
-- >     ...
local :: Defs f => DefM f (f t) -> f t
local m = unliftDS $ unDefM m liftDS

-- | Monads for managing variable names
class Monad m => VarM m where
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

-- | A general pretty-printer for 'Defs' methods. Use different @m@ printing different HOAS, to avoid overlapping instance.
newtype PprDefs m _a = PprDefs {pprDefs :: D.Precedence -> m D.Doc}

data RPairD = RPairD D.Doc D.Doc | ROtherD D.Doc

pprRPairD :: RPairD -> D.Doc
pprRPairD (RPairD d1 d2) = D.hcat [ D.align d1, D.text "<|", D.align d2 ] -- D.hcat [D.text "<", D.align d1 D.<$$> D.text ",", D.align d2, D.text ">"]
pprRPairD (ROtherD d)    = d

-- FIXME: The current pretty-printer does not output "let rec ... and ...", which makes outputs unreadable.
instance VarM m => Defs (PprDefs m) where
  newtype Fs (PprDefs m) _a = PRules {runPRules :: D.Precedence -> m RPairD}

  liftDS a = PRules $ \k -> do
    d <- pprDefs a 10
    return $ ROtherD $ D.parensIf (k > 9) $ D.text "↑" D.<> D.align d

  unliftDS r = PprDefs $ \k -> do
    d <- pprRPairD <$> runPRules r 10
    return $ D.parensIf (k > 9) $ D.text "↓" D.<> D.align d

  consDS r1 r2 = PRules $ \_ -> do
    -- d1 <- pprRPairD <$> runPRules r1 0
    d1 <- pprDefs r1 10
    d2 <- pprRPairD <$> runPRules r2 0
    return $ RPairD d1 d2

  letrDS f = PRules $ \k -> do
    x <- newVar
    res <- nestScope $ runPRules (f (PprDefs $ \_ -> return $ D.text x)) 0
    return $
      ROtherD $
        D.parensIf (k > 0) $ case res of
          RPairD d1 d2 ->
            D.align $
              D.group $
                D.hsep [D.text "let rec", D.text x, D.text "=", D.align d1, D.text "in"]
                  D.</> D.align d2
          ROtherD d ->
            D.align $ D.group $ D.text "letr" D.<+> D.text x <> D.text "." D.</> D.nest 2 (D.align d)
