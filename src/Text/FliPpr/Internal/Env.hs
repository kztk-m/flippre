{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

-- |
-- A file that contains manipulation of environments.
-- The file intentionally uses some unsafe features in Haskell.
module Text.FliPpr.Internal.Env where

import           Control.Applicative   (Const (..))
import           Control.Category
import           Data.Coerce           (coerce)
import           Data.Functor.Identity (Identity (..))
import           Data.IntMap           (IntMap)
import qualified Data.IntMap           as IM
import           Data.Kind
import           Data.Maybe            (fromJust, fromMaybe)
import           Data.Monoid           (Endo (..))
import           Data.Typeable         (Proxy (..), (:~:) (..))
import           Prelude               hiding (id, (.))
import           Text.FliPpr.Doc
import           Unsafe.Coerce         (unsafeCoerce)

-- | A common implementation works in general.
newtype VarTT i env env' = VarTT {runVarTT :: forall a. Var i env a -> Var i env' a}

class Category (VarT i) =>  EnvImpl (i :: k -> Type) where
  data Var i :: [k] -> k -> Type
  data Rep i :: [k] -> Type
  data Env i :: (k -> Type) -> [k] -> Type
  data VarT i :: [k] -> [k] -> Type

  runVarT :: VarT i env env' -> Var i env a -> Var i env' a

  showVar :: Var i env a -> String
  eqVar :: Var i env a -> Var i env b -> Maybe (a :~: b)

  lookupEnv :: Var i env a -> Env i f env -> f a

  updateEnv :: Var i env a -> f a -> Env i f env -> Env i f env
  updateEnv x v = modifyEnv x (const v)

  modifyEnv :: Var i env a -> (f a -> f a) -> Env i f env -> Env i f env
  modifyEnv x f env = updateEnv x (f (lookupEnv x env)) env

  mapEnv :: (forall a. f a -> g a) -> Env i f env -> Env i g env
  mapEnv f env = runIdentity $ traverseWithVar (\_ -> Identity . f) env

  traverseWithVar :: Applicative m => (forall a. Var i env a -> f a -> m (g a)) -> Env i f env -> m (Env i g env)

  zipWithA :: Applicative m => (forall a. f a -> g a -> m (h a)) -> Env i f env -> Env i g env -> m (Env i h env)

  emptyEnv :: Env i f '[]

  emptyRep :: Rep i '[]
  emptyRep = repOf emptyEnv


  diffRefl :: VarT i env env
  diffRefl = id

  diffStep :: VarT i env env' -> VarT i env (a : env')

  extendRep :: Rep i env -> Proxy a -> Rep i (a : env)

  varZ :: Rep i env -> Var i (a : env) a

  -- | Extending environment. It returns a triple of a new environment, a
  -- newly-introduced variable, and a witness that the new environment is one bigger than the original.
  extendEnv :: Env i f env -> f a -> (Env i f (a : env), Var i (a : env) a, VarT i env (a : env))

  repOf :: Env i f env -> Rep i env

  -- | Computes the difference of two environments, as a 'VarT'.
  --   This function only succeeds when @env'@ is bigger than @env@.
  diffRep :: Rep i env -> Rep i env' -> VarT i env env'

class Shiftable d t where
  shift :: VarT d env env' -> t env a -> t env' a

instance EnvImpl d => Shiftable d (Var d) where
  shift = runVarT

class DeBruijnIndex v where
  vz :: v (a : env) a
  vs :: v env a -> v (b : env) a

instance DeBruijnIndex (Var U) where
  vz = VarU 0
  vs (VarU i) = VarU (i + 1)

instance Category (VarTT d) where
  id = VarTT id
  VarTT f . VarTT g = VarTT (f . g)

data U k -- Unsafe

data Untype = forall a. Untype a

unsafeCast :: Untype -> a
unsafeCast (Untype a) = unsafeCoerce a

instance Category (VarT U) where
  id = VarTU 0
  VarTU n . VarTU m = VarTU (n + m)

instance EnvImpl U where
  newtype Var U _ _ = VarU Int

  data Env U _ _ = EnvU {-# UNPACK #-} !Int !(IntMap Untype)

  -- ith var corresponds to (k-i)th index.
  newtype Rep U _ = RepU Int

  newtype VarT U _ _ = VarTU Int

  runVarT (VarTU i) (VarU n) = VarU (i + n)
  {-# INLINE runVarT #-}

  showVar (VarU n) = show n
  eqVar (VarU n) (VarU m) =
    if n == m
      then unsafeCoerce (Just Refl)
      else Nothing

  lookupEnv (VarU n) (EnvU k m) = unsafeCast (fromJust $ IM.lookup (k - n) m)

  modifyEnv (VarU n) f (EnvU k m) = EnvU k (IM.adjust (Untype . f . unsafeCast) (k - n) m)

  traverseWithVar f (EnvU k m) = EnvU k <$> IM.traverseWithKey (\i x -> Untype <$> f (VarU (k - i)) (unsafeCast x)) m

  mapEnv f (EnvU k m) = EnvU k $ IM.map (Untype . f . unsafeCast) m

  zipWithA f (EnvU k m1) (EnvU _ m2) =
    fmap (EnvU k) $ sequenceA $ IM.intersectionWith (\x y -> Untype <$> f (unsafeCast x) (unsafeCast y)) m1 m2

  -- I don't know why (-1) is used here.
  emptyEnv = EnvU (-1) IM.empty
  {-# INLINE emptyEnv #-}

  emptyRep = RepU (-1)
  {-# INLINE emptyRep #-}

  extendRep (RepU k) _ = RepU (k + 1)

  extendEnv (EnvU k m) v = (EnvU (k + 1) (IM.insert (k + 1) (Untype v) m), VarU 0, VarTU 1)
  {-# INLINE extendEnv #-}

  diffStep (VarTU k) = VarTU (k + 1)

  repOf (EnvU k _) = RepU k
  {-# INLINE repOf #-}

  varZ _ = VarU 0

  diffRep (RepU k) (RepU k') = VarTU $ k' - k
    -- VarTU $ VarTT $ \(VarU i) -> VarU (i + (k' - k))
  {-# INLINE diffRep #-}



-- | *U*nsafe implementing using de Bruijn levels
data UL k

instance Category (VarT UL) where
  id    = VarTUL ()
  _ . _ = VarTUL ()

instance EnvImpl UL where
  newtype Var UL _ _ = VarUL Int

  data Env UL _ _ = EnvUL {-# UNPACK #-} !Int !(IntMap Untype)

  newtype Rep UL _ = RepUL Int

  -- Here, shifting does not check any representation ...
  newtype VarT UL _ _ = VarTUL ()

  runVarT _ (VarUL x) = VarUL x

  showVar (VarUL n) = show n
  eqVar (VarUL n) (VarUL m) =
    if n == m
      then unsafeCoerce (Just Refl)
      else Nothing

  lookupEnv (VarUL i) (EnvUL _ m) = unsafeCast (fromJust $ IM.lookup i m)

  modifyEnv (VarUL i) f (EnvUL k m) = EnvUL k (IM.adjust (Untype . f . unsafeCast) i m)

  traverseWithVar f (EnvUL k m) = EnvUL k <$> IM.traverseWithKey (\i x -> Untype <$> f (coerce i) (unsafeCast x)) m

  zipWithA f (EnvUL k m1) (EnvUL _ m2) =
    fmap (EnvUL k) $ sequenceA $ IM.intersectionWith (\x y -> Untype <$> f (unsafeCast x) (unsafeCast y)) m1 m2


  emptyEnv = EnvUL 0 IM.empty
  extendEnv (EnvUL k m) v = (EnvUL (k + 1) (IM.insert k (Untype v) m), VarUL k, VarTUL ())

  diffStep _ = VarTUL ()

  extendRep (RepUL k) _ = RepUL (k + 1)

  varZ (RepUL k) = VarUL k

  repOf (EnvUL k _) = RepUL k

  diffRep _ _ = VarTUL ()



-- | Safe(r) implementation
data S k

instance EnvImpl S where
  data Var S :: [k] -> k -> Type where
    VZ :: Var S (a : env) a
    VS :: Var S env a -> Var S (b : env) a

  data Env S :: (k -> Type) -> [k] -> Type where
    EEnd :: Env S f '[]
    EExtend :: Env S f env -> f a -> Env S f (a : env)

  newtype VarT S env env' = VarTS (VarTT S env env')
    deriving Category

  newtype Rep S env = SRep (Env S Proxy env)

  runVarT = runVarTT . coerce

  eqVar VZ VZ         = Just Refl
  eqVar (VS n) (VS m) = eqVar n m
  eqVar _ _           = Nothing

  showVar = show . go
    where
      go :: Var S env a -> Int
      go VZ     = 0
      go (VS n) = 1 + go n

  lookupEnv VZ (EExtend _ v)     = v
  lookupEnv (VS n) (EExtend e _) = lookupEnv n e

  modifyEnv VZ f (EExtend e v)     = EExtend e (f v)
  modifyEnv (VS n) f (EExtend e v) = EExtend (modifyEnv n f e) v

  traverseWithVar _ EEnd = pure EEnd
  traverseWithVar fn (EExtend e v) = go fn e v (coerce $ VarTT id)
    where
      go :: Applicative m => (forall t. Var S env t -> f t -> m (g t)) -> Env S f def -> f a -> VarT S (a : def) env -> m (Env S g (a : def))
      go f EEnd t sh = EExtend EEnd <$> f (runVarT sh VZ) t
      go f (EExtend rest t') t sh =
        EExtend <$> go f rest t' (sh . coerce (VarTT VS)) <*> f (runVarT sh VZ) t

  zipWithA _ EEnd EEnd = pure EEnd
  zipWithA f (EExtend e v) (EExtend e' v') =
    EExtend <$> zipWithA f e e' <*> f v v'

  emptyEnv = EEnd
  extendEnv e v = (EExtend e v, VZ, coerce (VarTT VS))

  varZ _ = VZ

  diffStep i = coerce $ VarTT (VS . runVarT i)

  repOf = SRep . mapEnv h
    where
      h :: f a -> Proxy a
      h _ = Proxy

  extendRep = coerce EExtend

  --   repOf EEnd          = REnd
  --   repOf (EExtend e _) = RExtend (repOf e) Proxy

  diffRep (SRep rep1) (SRep rep2) = go (len rep2 - len rep1) rep1 rep2
    where
      len :: Env S f env -> Int
      len EEnd          = 0
      len (EExtend e _) = len e + 1

      go :: Int -> Env S Proxy env -> Env S Proxy env' -> VarT S env env'
      go 0 _ _               = unsafeCoerce $ VarTS $ VarTT id
      go n r1 (EExtend r2 _) = coerce (VarTT VS) . go (n -1) r1 r2
      go _ _ _               = error "diffRep: violated invariant."


foldEnvWithVar ::
  (EnvImpl rep, Monoid m) =>
  (forall a. Var rep def a -> f a -> m) ->
  Env rep f def ->
  m
foldEnvWithVar f = getConst . traverseWithVar (\v e -> Const (f v e))
{-# INLINE foldEnvWithVar #-}

foldEnv :: (EnvImpl rep, Monoid m) => (forall a. f a -> m) -> Env rep f def -> m
foldEnv f = foldEnvWithVar (const f)
{-# INLINE foldEnv #-}

foldrEnv :: (EnvImpl rep) => (forall a. f a -> b -> b) -> b -> Env rep f def -> b
foldrEnv f = flip $ appEndo . foldEnv (Endo . f)
{-# INLINE foldrEnv #-}

foldrEnvWithVar :: (EnvImpl rep) => (forall a. Var rep def a -> f a -> b -> b) -> b -> Env rep f def -> b
foldrEnvWithVar f = flip $ appEndo . foldEnvWithVar (\k x -> Endo (f k x))
{-# INLINE foldrEnvWithVar #-}


pprEnv :: forall rep d f def. (EnvImpl rep, DocLike d) => (forall a. String -> f a -> d) -> Env rep f def -> d
pprEnv pprBody = fromMaybe empty . foldrEnvWithVar h Nothing
  where
    h :: forall env a. Var rep env a -> f a -> Maybe d -> Maybe d
    h v body r =
      let rd = align (pprBody (showVar v) body)
      in Just $ case r of
           Nothing -> rd
           Just d  -> d $$ rd

