{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE NoMonomorphismRestriction  #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

module Text.FliPpr.Internal.Defs
  ( -- * Definitions
    Defs (..),
    DefM (..),
    Tip(..),

    -- * Normalized form
    NDefs(..) , Norm(..),

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
    Arg(..),

    -- ** Low-level primitives
    letr1, letrs,

    -- -- * Mapping functios
    -- TransD,

    -- * Pretty-printing
    VarM (..),
    PprExp (..), pattern PprExpN, pprExpN
  )
where

import           Data.Functor.Identity      (Identity (..))

import           Control.Applicative        (Alternative (..))
import qualified Data.Fin                   as F
import           Data.Int                   (Int8)
import           Data.Kind                  (Type)
import qualified Data.Type.Nat              as F
import           Data.Word                  (Word8)
import qualified Text.FliPpr.Doc            as D

import           Data.Coerce                (coerce)
import           Data.Functor.Const         (Const)

import           Text.FliPpr.Internal.HList

-- | Nested products of @f@ types.
--
--   The argument of 'VT' and the first argument of 'VCons' are intensionally lazy, as
--   we may want to use Haskell's recursive definitions to implement 'letrDS'.


-- | A class to control looping structure. The methods are not supposed to be used directly, but via derived forms.
class Defs (f :: k -> Type) where
  -- | Interpretation of product types. We are expecting that
  -- @Fs f a@ is isomorphic to @forall r. (DTypeVal f a -> f r) -> f r@,
  -- but having direct interpretation would be convenient, at least to define 'letrDS'.
  data D f :: [k] -> k -> Type
  -- D stands for "direct style".

  -- By kztk @ 2020-11-26
  -- We will use the following methods for recursive definitions
  -- By kztk @ 2021-02-17
  -- Use the standard lists instead of special datatypes.

  liftD   :: f a -> D f '[] a
  unliftD :: D f '[] a -> f a

  consD :: f a -> D f as r -> D f (a ': as) r

  -- | A method inspired by the trace operator in category theory (it is named
  -- after "let rec" and "trace"), a basic building block of mutual recursions.
  letrD :: (f a -> D f (a : as) r) -> D f as r

newtype Norm e a = Norm { unNorm :: e a }

class NDefs (f :: k -> Type) where
  data ND f :: [k] -> k -> Type

  defN   :: HList f as -> f a -> ND f as a
  localN :: ND f '[] a -> f a
  letrN  :: (f a -> ND f (a : as) r) -> ND f as r

-- Normalization
instance NDefs f => Defs (Norm f) where
  newtype D (Norm f) as a = FromND { fromND :: forall bs. (HList f as -> HList f bs) -> ND f bs a }

  liftD e   = FromND $ \k -> defN (k HNil) (unNorm e)
  unliftD d = Norm $ localN $ fromND d id
  consD e d = FromND $ \k -> fromND d (k . HCons (unNorm e))
  letrD h   = FromND $ \k -> letrN $ \a -> fromND (h $ Norm a) $ \(HCons ex r) -> HCons ex (k r)



-- | A monad to give better programming I/F. This actually is a specialized version of a codensity monad: @Def f@ is @Codensity (Fs f)@.
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
letr1 :: Defs f => (f a -> DefM f (f a, r)) -> DefM f r
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

-- | @def a@ is a synonym of @fmap (a,)@, which is convenient to be used with 'letr'.
def :: Functor f => a -> f b -> f (a, b)
def a = fmap (a,)
{-# INLINE def #-}

-- -- | @TransD f a@ maps @f@ to leaves in @a@. For example, @TransD f (Lift a ** Lift b) = (Lift (f a) ** Lift (f b))@.
-- type family TransD f a = b | b -> a f where
--   TransD f ( 'T a) = 'T (f a)
--   TransD f (a <* b) = f a <* TransD f b

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
class Defs f => Arg f t where
  letr :: (t -> DefM f (t, r)) -> DefM f r

instance Defs f => Arg f () where
  letr f = snd <$> f ()

newtype Tip a = Tip { unTip :: a }

instance Defs f => Arg f (Tip (f a)) where
  letr :: forall r. (Tip (f a) -> DefM f (Tip (f a), r)) -> DefM f r
  letr f = letr1 (coerce f :: f a -> DefM f (f a, r))

instance (Arg f a, Arg f b) => Arg f (a, b) where
  letr f = letr $ \b -> letr $ \a -> do
                ((a', b'), r) <- f (a, b)
                return (a', (b', r))

instance (Arg f a, Arg f b, Arg f c) => Arg f (a, b, c) where
  letr f = letr $ \c -> letr $ \b -> letr $ \a -> do
    ((a', b', c'), r) <- f (a, b, c)
    return (a', (b', (c', r)))

instance (Arg f a, Arg f b, Arg f c, Arg f d) => Arg f (a, b, c, d) where
  letr f = letr $ \ ~(c,d) -> letr $ \ ~(a,b) -> do
    ((a', b', c', d'), r) <- f (a, b, c, d)
    return ( (a', b'), ( (c', d'), r ) )

instance (Arg f a1, Arg f a2, Arg f a3, Arg f a4, Arg f a5) => Arg f (a1, a2, a3, a4, a5) where
  letr f = letr $ \ ~(a4,a5) -> letr $ \ ~(a1, a2, a3) -> do
    ((b1, b2, b3, b4, b5), r) <- f (a1, a2, a3, a4, a5)
    return ( (b1, b2, b3), ( (b4, b5), r ) )

instance (Arg f a1, Arg f a2, Arg f a3, Arg f a4, Arg f a5, Arg f a6) => Arg f (a1, a2, a3, a4, a5, a6) where
  letr f = letr $ \ ~(a4,a5, a6) -> letr $ \ ~(a1, a2, a3) -> do
    ((b1, b2, b3, b4, b5, b6), r) <- f (a1, a2, a3, a4, a5, a6)
    return ( (b1, b2, b3), ( (b4, b5, b6), r ) )


-- | @letrs [k1,...,kn] $ \f -> (def fdef r)@ to mean
--
-- > letr $ \f1 -> letr $ \f2 -> ... letr $ \fn ->
-- >   def (fdef k1) >>> ... >>> def (fdef kn) $ do
-- >   let f k = fromJust $ lookup k [(k1,f1), ..., (kn,fn)]
-- >   r
letrs :: (Eq k, Arg f a) => [k] -> ((k -> a) -> DefM f (k -> a, r)) -> DefM f r
letrs [] h     = snd <$> h (const $ error "Text.FliPpr.Internal.Defs.letrs: out of bounds")
letrs (k:ks) h = letr $ \fk -> letrs ks $ \f -> do
  (f', r) <- h $ \x -> if x == k then fk else f x
  return (f', (f' k, r))


newtype FromBounded b = FromBounded { getBounded :: b } deriving (Eq, Ord, Enum, Bounded, Num, Real, Integral, Show)

letrsB :: (Eq b, Enum b, Bounded b, Arg f a) =>
          ((b -> a) -> DefM f (b -> a, r)) -> DefM f r
letrsB = letrs [minBound..maxBound]

instance (Eq b, Enum b, Bounded b, Arg f a) => Arg f (FromBounded b -> a) where
  letr = letrsB

-- Instances of concrete bounded types: we don't make instances like Arg f (Int -> a),
-- as they are unrealistic.

instance Arg f a => Arg f (Bool -> a) where
  letr = letrsB

instance (Arg f a, F.SNatI m, 'F.S m ~ n) => Arg f (F.Fin n -> a) where
  letr = letrsB

instance Arg f a => Arg f (Word8 -> a) where
  letr = letrsB

instance Arg f a => Arg f (Int8 -> a) where
  letr = letrsB

instance Arg f a => Arg f (() -> a) where
  letr = letrsB

instance Arg f (b -> a)  => Arg f (Identity b -> a) where
  letr :: forall r. ((Identity b -> a) -> DefM f (Identity b -> a, r)) -> DefM f r
  letr h = letr (coerce h :: (Identity b -> a) -> DefM f (Identity b -> a, r))

instance Arg f (b -> a) => Arg f (Const b x -> a) where
  letr :: forall r. ((Const b x -> a) -> DefM f (Const b x -> a, r)) -> DefM f r
  letr h = letr (coerce h :: (Const b x -> a) -> DefM f (Const b x -> a , r))


-- | A variant of 'mfix'. This function is supported to be used as:
--
--- > {-# LANGUAGE RecursiveDo, RebindableSyntax #-}
--  >
--  > someFunc = do
--  >     rec a <- share $ ... a ... b ...
--  >         b <- share $ ... a ... b ...
--  >     ...
--  >   where mfix = mfixDefM
mfixDefM :: (Defs f, Arg f a) => (a -> DefM f a) -> DefM f a
mfixDefM f = letr $ \a -> (,a) <$> f a

-- | 'share's computation.
share :: Defs f => f a -> DefM f (f a)
share s = DefM $ \k -> letrD $ \a -> consD s (k a)

-- | Makes definions to be 'local'.
--
-- For example, in the follownig code, the scope of shared computation is limited to @foo@; so using @foo@ twice copies @defa@.
--
-- > foo = local $ do
-- >    a <- share defa
-- >     ...
local :: Defs f => DefM f (f t) -> f t
local m = unliftD $ unDefM m liftD

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
newtype PprExp m _a = PprExp {pprExp :: D.Precedence -> m D.Doc}

pattern PprExpN :: (D.Precedence  -> m D.Doc) -> Norm (PprExp m) a
pattern PprExpN a = Norm (PprExp a)


pprExpN :: Norm (PprExp m) a -> D.Precedence  -> m D.Doc
pprExpN = pprExp . unNorm

instance VarM m => NDefs (PprExp m) where
  newtype ND (PprExp m) _as _a = PDefs { pdefs :: [String] -> D.Precedence  -> m D.Doc }

  defN exps r = PDefs $ \xs k -> do
    bs <- D.vcat <$> go xs exps
    dr <- pprExp r 0

    pure $ D.parensIf (k > 0) $ D.align $
            D.vcat [D.text "let" D.<+> D.align bs,
                    D.text "in" D.<+> dr ]
    where
      go :: VarM m => [String] -> HList (PprExp m) as -> m [D.Doc]
      go _ HNil                = pure[]
      go (x : xs) (HCons e es) = do
        de  <- pprExp e 0
        res <- go xs es
        pure $ (D.text x D.<+> D.text "=" D.<+> D.align de) : res
      go _ _                   = error "Unreachable"

  localN d = PprExp $ \k ->
    pdefs d [] k
  letrN h = PDefs $ \xs k -> do
    x <- newVar
    nestScope $ pdefs (h (PprExp $ \_ -> pure $ D.text x))  (x : xs) k

-- data RPairD = RPairD D.Doc D.Doc | ROtherD D.Doc

-- pprRPairD :: RPairD -> D.Doc
-- pprRPairD (RPairD d1 d2) = D.hcat [ D.align d1, D.text "<|", D.align d2 ] -- D.hcat [D.text "<", D.align d1 D.<$$> D.text ",", D.align d2, D.text ">"]
-- pprRPairD (ROtherD d)    = d


-- -- FIXME: The current pretty-printer does not output "let rec ... and ...", which makes outputs unreadable.
-- instance VarM m => Defs (PprExp m) where
--   newtype D (PprExp m) _as _a = PRules {runPRules :: D.Precedence -> m RPairD}

--   liftD a = PRules $ \k -> do
--     d <- pprExp a 10
--     return $ ROtherD $ D.parensIf (k > 9) $ D.text "↑" D.<> D.align d

--   unliftD r = PprExp $ \k -> do
--     d <- pprRPairD <$> runPRules r 10
--     return $ D.parensIf (k > 9) $ D.text "↓" D.<> D.align d

--   consD r1 r2 = PRules $ \_ -> do
--     -- d1 <- pprRPairD <$> runPRules r1 0
--     d1 <- pprExp r1 10
--     d2 <- pprRPairD <$> runPRules r2 0
--     return $ RPairD d1 d2

--   letrD f = PRules $ \k -> do
--     x <- newVar
--     res <- nestScope $ runPRules (f (PprExp $ \_ -> return $ D.text x)) 0
--     return $
--       ROtherD $
--         D.parensIf (k > 0) $ case res of
--           RPairD d1 d2 ->
--             D.align $
--               D.group $
--                 D.hsep [D.text "let rec", D.text x, D.text "=", D.align d1, D.text "in"]
--                   D.</> D.align d2
--           ROtherD d ->
--             D.align $ D.group $ D.text "letr" D.<+> D.text x <> D.text "." D.</> D.nest 2 (D.align d)
