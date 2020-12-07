{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

module Text.FliPpr.Internal.Defs
  ( -- * Definitions
    DType (..),
    DTypeVal (..),
    Defs (..),
    DefM (..),
    type (**),
    type Lift,

    -- * Helper functions for defining 'Alternative' instances
    manyD,
    someD,

    -- * 'DType'-indexed functions
    DefType (..),
    shareM,
    shareDef,
    letrGen,
    letrG,

    -- * Manipulation of rules
    Rules,

    -- ** High-level I/F
    share,
    local,
    rule,
    nt,
    fixDef,
    mfixDefM,
    shareGen,
    Convertible (..),

    -- ** Low-level primitives
    letr, letrs, letrR,
    lift,
    unlift,
    pairRules,
    unpairRulesM,

    -- * Mapping functios
    rmap,
    vmap,
    TransD,

    -- * Pretty-printing
    VarM (..),
    PprDefs (..),
  )
where

import           Control.Applicative (Alternative (..))
import           Control.Monad       ((>=>))
import qualified Control.Monad
import           Data.Kind           (Type)
import qualified Text.FliPpr.Doc     as D

-- | A type for (mutually recursive) definitions
data DType ft
  = -- | Type lifted from @ft@
    T ft
  | -- | Expressions that may share some definitions
    DType ft :*: DType ft

type a ** b = a ':*: b

type Lift a = 'T a

infixr 4 **

infixr 4 :*:

data DTypeVal (f :: ft -> Type) :: DType ft -> Type where
  VT :: f ft -> DTypeVal f ( 'T ft)
  VProd :: DTypeVal f a -> DTypeVal f b -> DTypeVal f (a ** b)

class Defs (f :: k -> Type) | f -> k where
  data Fs f :: DType k -> Type

  -- By kztk @ 2020-11-26
  -- We will use the following methods for recursive definitions
  liftDS :: f a -> Fs f ( 'T a)
  unliftDS :: Fs f ( 'T a) -> f a

  pairDS :: Fs f a -> Fs f b -> Fs f (a ** b)

  --   unpairRules :: (DefType a, DefType b) => Rules exp (a :*: b) -> (Rules exp a -> Rules exp b -> Rules exp r) -> Rules exp r

  -- A method inspired by the trace operator in category theory.
  -- This method serves as a bulding block of mutual recursions
  letrDS :: (f a -> Fs f ( 'T a ** r)) -> Fs f r

-- In implementation, it is a specialized version of a codensity monad.
newtype DefM f a = DefM {unDefM :: forall r. DefType r => (a -> Fs f r) -> Fs f r}

-- | 'DefM' is a monad to make definitions easily.
--   We intentionally do not make it an instance of 'MonadFix'.
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


type Rules f a = DefM f (DTypeVal f a)

lift :: f a -> Rules f ( 'T a)
lift x = DefM $ \k -> k (VT x)

unlift :: Defs f => Rules f ( 'T a) -> f a
unlift x = unliftDS $ unDefM x $ \(VT y) -> liftDS y

pairRules :: Rules f a -> Rules f b -> Rules f (a ** b)
pairRules x y = DefM $ \k -> unDefM x $ \a -> unDefM y $ \b -> k (VProd a b)

-- letr :: Defs f => (f a -> Rules f ( 'T a ** r)) -> Rules f r
letr :: Defs f => (f a -> DefM f (f a, r)) -> DefM f r
letr h = DefM $ \k -> letrDS $ \a -> unDefM (h a) $ \(b, r) -> pairDS (liftDS b) (k r)

letrs :: (Defs f, Eq k) => [k] -> ((k -> f a) -> DefM f (k -> f a, r)) -> DefM f r
letrs [] h = snd <$> h (const $ error "Text.FliPpr.Internal.Defs.letrs: out of bounds")
letrs (k:ks) h = letr $ \fk -> letrs ks $ \h' -> do
  (dh'', r) <- h $ \x -> if x == k then fk else h' x
  return (dh'', (dh'' k, r))

letrR :: Defs f => (f a -> Rules f ( 'T a ** r)) -> Rules f r
letrR h = letr $ h >=> \case { VProd (VT a) r -> return (a, r) }

-- | A variant of 'many' defined without Haskell-level recursion.
manyD :: (Defs f, Alternative f) => f a -> f [a]
manyD d = unlift $ letr $ \a -> return (pure [] <|> (:) <$> d <*> a, VT a)

-- | A variant of 'some' defined without Haskell-level recursion.
someD :: (Defs f, Alternative f) => f a -> f [a]
someD d = unlift $ letr $ \m -> letr $ \s ->
   p ((:) <$> d <*> m) $
   p (pure [] <|> s) $
   return (VT s)
   where
     p a = fmap (a,)
   -- letr $ \x -> return (d, VT $ (:) <$> x <*> manyD x)
  -- pairRules (lift d) $ lift $ (:) <$> a <*> manyD a

type family TransD f a = b | b -> a f where
  TransD f ( 'T a) = 'T (f a)
  TransD f (a ** b) = TransD f a ** TransD f b

class DefType (r :: DType k) where
  indDType ::
    forall f.
    (forall a. f ( 'T a)) ->
    (forall a b. (DefType a, DefType b) => f (a ** b)) ->
    f r

instance DefType ( 'T a) where
  indDType f _ = f

instance (DefType a, DefType b) => DefType (a ** b) where
  indDType _ step = step

newtype LetG f a = LetG (forall r. (DTypeVal f a -> DefM f (DTypeVal f a,r)) -> DefM f r)

letrG :: (Defs f, DefType a) => (DTypeVal f a -> DefM f (DTypeVal f a, r)) -> DefM f r
letrG = let LetG f = indDType letrG1 letrGStep in f
  where
    letrG1 :: Defs f => LetG f ('T t)
    letrG1 = LetG $ \h -> letr $ \x -> h (VT x) >>= \case { (VT a, r) -> return (a, r) }

    letrGStep :: (DefType a, DefType b, Defs f) => LetG f (a ** b)
    letrGStep = LetG $ \h -> letrG $ \b -> letrG $ \a -> arr <$> h (VProd a b)

    arr :: (DTypeVal f (a ** b), r) -> (DTypeVal f a, (DTypeVal f b, r))
    arr (VProd a b, r) = (a, (b, r))


newtype LetRGen f a = LetRGen (forall r. (DTypeVal f a -> Rules f (a ** r)) -> Rules f r)

letrGen :: (Defs f, DefType a) => (DTypeVal f a -> Rules f (a ** r)) -> Rules f r
letrGen =
  let LetRGen f = indDType letrGen0 letrGenStep in f
  where
    letrGen0 :: Defs f => LetRGen f ( 'T t)
    letrGen0 = LetRGen $ \h -> letrR (h . VT)

    letrGenStep :: (DefType a, DefType b, Defs f) => LetRGen f (a ** b)
    letrGenStep = LetRGen $ \h -> letrGen $ \b -> letrGen $ \a -> assocr $ h (VProd a b)
      where
        assocr :: Rules f ((a ** b) ** r) -> Rules f (a ** (b ** r))
        assocr x = DefM $ \k -> unDefM x $ \(VProd (VProd a b) r) -> k (VProd a (VProd b r))


newtype VMap f k1 k2 a = VMap ((forall t. f (k1 t) -> f (k2 t)) -> DTypeVal f (TransD k1 a) -> DTypeVal f (TransD k2 a))

vmap :: forall f k1 k2 r. (Defs f, DefType r) => (forall t. f (k1 t) -> f (k2 t)) -> DTypeVal f (TransD k1 r) -> DTypeVal f (TransD k2 r)
vmap = let VMap f = indDType vmap0 vmapStep in f
  where
    vmap0 :: Defs f => VMap f k1 k2 ( 'T t)
    vmap0 = VMap $ \f (VT x) -> VT (f x)

    vmapStep :: forall a b. (Defs f, DefType a, DefType b) => VMap f k1 k2 (a ** b)
    vmapStep = VMap $ \f (VProd a b) -> VProd (vmap f a) (vmap f b)

rmap :: forall f k1 k2 a. (DefType a, Defs f) => (forall t. f (k1 t) -> f (k2 t)) -> Rules f (TransD k1 a) -> Rules f (TransD k2 a)
rmap f x = DefM $ \k -> unDefM x (k . vmap f)

shareDef :: (DefType a, Defs f) => Rules f a -> (DTypeVal f a -> Rules f r) -> Rules f r
shareDef a h = letrGen (pairRules a . h)

fixDef :: (DefType a, Defs f) => (DTypeVal f a -> Rules f a) -> Rules f a
fixDef h = letrGen $ \x -> pairRules (h x) (return x)

runDefM :: DefType r => DefM exp (Rules exp r) -> Rules exp r
runDefM = Control.Monad.join -- unDefM m id

unpairRulesM :: (Defs exp, DefType a, DefType b) => Rules exp (a ** b) -> DefM exp (Rules exp a, Rules exp b)
unpairRulesM r = DefM $ \k -> unDefM r $ \(VProd a b) -> k (DefM $ \k1 -> k1 a, DefM $ \k2 -> k2 b)

-- unpairRules r $ curry k

class Convertible f a s | s -> a where
  fromDTypeVal :: DTypeVal f a -> s
  toDTypeVal :: s -> DefM f (DTypeVal f a)

-- fromRules :: Rules f a -> DefM f b
-- toRules :: b -> Rules f a

mfixDefM :: (Defs f, DefType a, Convertible f a s) => (s -> DefM f s) -> DefM f s
mfixDefM h = fmap fromDTypeVal $ fixDef $ (>>= toDTypeVal) . h . fromDTypeVal

-- fromRules $ fixDef $ \a -> (fromRules a >>= h) >>= toRules

--  fromRules $ fixDef (\a -> unDefM (fromRules a >>= h) toRules)

-- | 'share's computation.
share :: Defs f => f a -> DefM f (f a)
share s = DefM $ \k -> letrDS $ \a -> pairDS (liftDS s) (k a)

-- shareDef :: (DefType a, Defs f) => Rules f a -> (DTypeVal f a -> Rules f r) -> Rules f r
-- DefM f (DTypeVal f a) -> (DTypeVal f a -> DefM f (DTypeVal f a)) -> DefM f (DTypeVal f a)

-- return :: DTypeVal f a -> DefM f (DTypeVal f a)
-- (\x -> unDefM x id) :: DefM f (Fs f a) -> Fs f a
--
-- v2fs :: DTypeVal f a -> Fs f a
-- (\x -> unDefM x v2fs) :: Rules f a -> Fs f a

newtype ShareM f a = ShareM (DTypeVal f a -> DefM f (DTypeVal f a))

shareM :: (Defs f, DefType a) => DTypeVal f a -> DefM f (DTypeVal f a)
shareM = let ShareM f = indDType shareM0 shareMStep in f
  where
    shareM0 :: Defs f => ShareM f ( 'T t)
    shareM0 = ShareM $ \(VT x) -> fmap VT (share x)

    shareMStep :: (Defs f, DefType a, DefType b) => ShareM f (a ** b)
    shareMStep =
      ShareM $ \(VProd a b) -> shareM a >>= \va -> shareM b >>= \vb -> return (VProd va vb)

shareGen :: forall f a s. (Defs f, DefType a, Convertible f a s) => s -> DefM f s
shareGen comp = fromDTypeVal <$> (shareM =<< toDTypeVal comp)

-- DefM $ \k -> shareDef (toRules @exp @a @s s) $ \a -> unDefM (fromRules @exp @a @s a) k

rule :: Defs f => f a -> DefM f (Rules f ( 'T a))
rule = shareGen . lift

nt :: Defs f => Rules f ( 'T a) -> f a
nt = unlift

local :: Defs f => DefM f (f t) -> f t
local m = unlift $ runDefM $ fmap lift m

instance Convertible f a (DTypeVal f a) where
  fromDTypeVal = id
  toDTypeVal = return

instance Convertible f a (Rules f a) where
  fromDTypeVal = return
  toDTypeVal = id

instance (Defs f, Convertible f a s, Convertible f b t) => Convertible f (a ** b) (s, t) where
  fromDTypeVal (VProd a b) = (fromDTypeVal a, fromDTypeVal b)
  toDTypeVal (s, t) = VProd <$> toDTypeVal s <*> toDTypeVal t

instance (Defs f, Convertible f a1 s1, Convertible f a2 s2, Convertible f a3 s3) => Convertible f (a1 ** a2 ** a3) (s1, s2, s3) where
  fromDTypeVal x = let (s1, (s2, s3)) = fromDTypeVal x in (s1, s2, s3)
  toDTypeVal (s1, s2, s3) = toDTypeVal (s1, (s2, s3))

instance (Defs f, Convertible f a1 s1, Convertible f a2 s2, Convertible f a3 s3, Convertible f a4 s4) => Convertible f (a1 ** a2 ** a3 ** a4) (s1, s2, s3, s4) where
  fromDTypeVal x = let (s1, (s2, (s3, s4))) = fromDTypeVal x in (s1, s2, s3, s4)
  toDTypeVal (s1, s2, s3, s4) = toDTypeVal (s1, (s2, (s3, s4)))

instance (Defs f, Convertible f a1 s1, Convertible f a2 s2, Convertible f a3 s3, Convertible f a4 s4, Convertible f a5 s5) => Convertible f (a1 ** a2 ** a3 ** a4 ** a5) (s1, s2, s3, s4, s5) where
  fromDTypeVal x = let (s1, (s2, (s3, (s4, s5)))) = fromDTypeVal x in (s1, s2, s3, s4, s5)
  toDTypeVal (s1, s2, s3, s4, s5) = toDTypeVal (s1, (s2, (s3, (s4, s5))))

instance
  (Defs f, Convertible f a1 s1, Convertible f a2 s2, Convertible f a3 s3, Convertible f a4 s4, Convertible f a5 s5, Convertible f a6 s6) =>
  Convertible f (a1 ** a2 ** a3 ** a4 ** a5 ** a6) (s1, s2, s3, s4, s5, s6)
  where
  fromDTypeVal x = let (s1, (s2, (s3, (s4, (s5, s6))))) = fromDTypeVal x in (s1, s2, s3, s4, s5, s6)
  toDTypeVal (s1, s2, s3, s4, s5, s6) = toDTypeVal (s1, (s2, (s3, (s4, (s5, s6)))))


-- | Monads for managing variable names
class Monad m => VarM m where
  -- | A new variable name, which may or may not differ in calls.
  --   For de Bruijn levels, use the Reader monad and define
  --
  --   @
  --      newVar = do {i <- ask ; return ("x" ++ show i ) }
  --   @
  --
  --   Just for using different names, use the State monad and define
  --   @
  --      newVar = do { i <- get ; put (i + 1) ; return ("x" ++ show i) }
  --   @
  --
  --   This representation does not cover de Bruijn indices; we do not support them.
  newVar :: m String

  -- | +1 to the nesting level. This is just identity if ones to assign different names for different variables.
  nestScope :: m a -> m a

newtype PprDefs m _a = PprDefs {pprDefs :: D.Precedence -> m D.Doc}

data RPairD = RPairD D.Doc D.Doc | ROtherD D.Doc

pprRPairD :: RPairD -> D.Doc
pprRPairD (RPairD d1 d2) = D.hcat [D.text "<", D.align d1 D.<$$> D.text ",", D.align d2, D.text ">"]
pprRPairD (ROtherD d) = d

instance VarM m => Defs (PprDefs m) where
  newtype Fs (PprDefs m) _a = PRules {runPRules :: D.Precedence -> m RPairD}

  liftDS a = PRules $ \k -> do
    d <- pprDefs a 10
    return $ ROtherD $ D.parensIf (k > 9) $ D.text "↑" D.<> D.align d

  unliftDS r = PprDefs $ \k -> do
    d <- pprRPairD <$> runPRules r 10
    return $ D.parensIf (k > 9) $ D.text "↓" D.<> D.align d

  pairDS r1 r2 = PRules $ \_ -> do
    d1 <- pprRPairD <$> runPRules r1 0
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
