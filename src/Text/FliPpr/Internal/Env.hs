{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- |
-- A file that contains manipulation of environments.
-- The file intentionally uses some unsafe features in Haskell.
module Text.FliPpr.Internal.Env where

import Control.Applicative (Const (..))
import Control.Category
import Data.Functor.Identity (Identity (..))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import Data.Kind
import Data.Maybe (fromJust, fromMaybe)
import Data.Monoid (Endo (..))
import Data.Typeable (Proxy (..), (:~:) (..))
import Text.FliPpr.Doc
import Unsafe.Coerce
import Prelude hiding (id, (.))

-- type Env' i t env = Env i t env env

{- Environments that can be mutually recursive -}
newtype VarT i env env' = VarT {runVarT :: forall a. Var i env a -> Var i env' a}

class EnvImpl (i :: k -> Type) where
  data Var i :: [k] -> k -> Type
  data Rep i :: [k] -> Type
  data Env i :: (k -> Type) -> [k] -> Type

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

  emptyEnv :: Env i f '[]

  -- | Extending environment. It returns a triple of a new environment, a
  -- newly-introduced variable, and a witness that the new environment is one bigger than the original.
  extendEnv :: Env i f env -> f a -> (Env i f (a : env), Var i (a : env) a, VarT i env (a : env))

  repOf :: Env i f env -> Rep i env

  -- | Computes the difference of two environments, as a 'VarT'.
  --   This function only succeeds when @env'@ is bigger than @env@.
  diffRep :: Rep i env -> Rep i env' -> VarT i env env'

class Shiftable d t where
  shift :: VarT d env env' -> t env a -> t env' a

instance Shiftable d (Var d) where
  shift = runVarT

class DeBruijnIndex v where
  vz :: v (a : env) a
  vs :: v env a -> v (b : env) a

instance DeBruijnIndex (Var U) where
  vz = VarU 0
  vs (VarU i) = VarU (i + 1)

-- instance DeBruijnIndex (Var S) where
--   vz = VZ
--   vs = VS

instance Category (VarT d) where
  id = VarT id
  VarT f . VarT g = VarT (f . g)

-- class EnvImpl i where
--   data Var i :: [Type] -> Type -> Type
--   data Env i :: ([Type] -> Type -> Type) -> [Type] -> [Type] -> Type
--   data Rep i :: [Type] -> Type

--   showVar :: Var i env a -> String
--   eqVar :: Var i env a -> Var i env b -> Maybe (a :~: b)

--   lookupEnv :: Var i def a -> Env i t use def -> t use a

--   modifyEnv :: Var i def a -> (t use a -> t use a) -> Env i t use def -> Env i t use def
--   modifyEnv x f env =
--     let res = lookupEnv x env
--     in updateEnv x (f res) env

--   updateEnv :: Var i def a -> t use a -> Env i t use def -> Env i t use def
--   updateEnv x v = modifyEnv x (const v)

--   traverseEnvWithVar ::
--     Applicative f =>
--     (forall a. Var i def a -> t use a -> f (t' use' a)) -> Env i t use def -> f (Env i t' use' def)

--   zipWithA :: Applicative f =>
--               (forall a. t use a -> t' use' a -> f (t'' use'' a)) ->
--               Env i t use def -> Env i t' use' def -> f (Env i t'' use'' def)

--   emptyEnv  :: Env i t use '[]
--   extendEnv :: Env i t use def -> t use a -> (Env i t use (a : def), Var i (a : def) a, VarT i def (a : def))

--   repOf :: Env i t use env -> Rep i env

--   -- env' must be bigger than or equal to env
--   embedVar :: Rep i env -> Rep i env' -> Var i env a -> Var i env' a

data U k -- Unsafe

data Untype = forall a. Untype a

unsafeCast :: Untype -> a
unsafeCast (Untype a) = unsafeCoerce a

instance EnvImpl U where
  newtype Var U _ _ = VarU Int

  data Env U _ _ = EnvU !Int (IntMap Untype)

  -- ith var corresponds to (k-i)th index.
  newtype Rep U _ = RepU Int

  showVar (VarU n) = show n
  eqVar (VarU n) (VarU m) =
    if n == m
      then unsafeCoerce (Just Refl)
      else Nothing

  lookupEnv (VarU n) (EnvU k m) = unsafeCast (fromJust $ IM.lookup (k - n) m)

  modifyEnv (VarU n) f (EnvU k m) = EnvU k (IM.adjust (Untype . f . unsafeCast) (k - n) m)

  traverseWithVar f (EnvU k m) = EnvU k <$> IM.traverseWithKey (\i x -> Untype <$> f (VarU (k - i)) (unsafeCast x)) m

  --   zipWithA f (EnvU k m1) (EnvU _ m2) =
  --     EnvU k <$> sequenceA (IM.unionWith (\x y -> fmap Untype $ f <$> (unsafeCast <$> x) <*> (unsafeCast <$> y)) (fmap pure m1) (fmap pure m2))

  emptyEnv = EnvU (-1) IM.empty
  extendEnv (EnvU k m) v = (EnvU (k + 1) (IM.insert (k + 1) (Untype v) m), VarU 0, VarT f)
    where
      f (VarU n) = VarU (n + 1)

  repOf (EnvU k _) = RepU k

  diffRep (RepU k) (RepU k') = VarT $ \(VarU i) -> VarU (i + (k' - k))

-- data M
data S k -- safe(r)

instance EnvImpl S where
  data Var S :: [k] -> k -> Type where
    VZ :: Var S (a : env) a
    VS :: Var S env a -> Var S (b : env) a

  data Env S :: (k -> Type) -> [k] -> Type where
    EEnd :: Env S f '[]
    EExtend :: Env S f env -> f a -> Env S f (a : env)

  newtype Rep S env = SRep (Env S Proxy env)

  eqVar VZ VZ = Just Refl
  eqVar (VS n) (VS m) = eqVar n m
  eqVar _ _ = Nothing

  showVar = show . go
    where
      go :: Var S env a -> Int
      go VZ = 0
      go (VS n) = 1 + go n

  lookupEnv VZ (EExtend _ v) = v
  lookupEnv (VS n) (EExtend e _) = lookupEnv n e

  modifyEnv VZ f (EExtend e v) = EExtend e (f v)
  modifyEnv (VS n) f (EExtend e v) = EExtend (modifyEnv n f e) v

  traverseWithVar _ EEnd = pure EEnd
  traverseWithVar f (EExtend e v) = go f e v (VarT id)
    where
      go :: Applicative m => (forall a. Var S env a -> f a -> m (g a)) -> Env S f def -> f a -> VarT S (a : def) env -> m (Env S g (a : def))
      go f EEnd t sh = EExtend EEnd <$> f (runVarT sh VZ) t
      go f (EExtend e t') t sh =
        EExtend <$> go f e t' (sh . VarT VS) <*> f (runVarT sh VZ) t

  --   zipWithA _ EEnd EEnd = pure EEnd
  --   zipWithA f (EExtend e v) (EExtend e' v') =
  --     EExtend <$> zipWithA f e e' <*> f v v'

  emptyEnv = EEnd
  extendEnv e v = (EExtend e v, VZ, VarT VS)

  repOf = SRep . mapEnv h
    where
      h :: f a -> Proxy a
      h _ = Proxy

  --   repOf EEnd          = REnd
  --   repOf (EExtend e _) = RExtend (repOf e) Proxy

  diffRep (SRep r1) (SRep r2) = go (len r2 - len r1) r1 r2
    where
      len :: Env S f env -> Int
      len EEnd = 0
      len (EExtend e _) = len e + 1

      go :: Int -> Env S Proxy env -> Env S Proxy env' -> VarT S env env'
      go 0 _ _ = unsafeCoerce $ VarT id
      go n r1 (EExtend r2 _) = VarT VS . go (n -1) r1 r2
      go _ _ _ = error "diffRep: violated invariant."

--   -- embedVar (RExtend REnd _) (RExtend REnd _) VZ     = unsafeCoerce VZ
--   -- embedVar (RExtend REnd v) (RExtend e _)    VZ     = VS (embedVar (RExtend REnd v) e VZ)
--   -- embedVar (RExtend e _)    (RExtend e' _)   (VS k) = VS (embedVar e e' k)
--   embedVar r1 r2 n =
--     case requal r1 r2 of
--       Just Refl -> n
--       _         ->
--         case r2 of
--           REnd -> error "Error: embedVar: violated assumption."
--           RExtend r2' _ -> VS (embedVar r1 r2' n)
-- --   embedVar _                _                _      = error "Error: embedVar: violated assumption."
--     where
--       requal :: Rep S env -> Rep S env' -> Maybe (env :~: env')
--       requal REnd REnd = Just Refl
--       requal (RExtend e _) (RExtend e' _) =
--         case requal e e' of
--           Just Refl -> Just (unsafeCoerce Refl)
--           Nothing   -> Nothing
--       requal _ _ = Nothing

-- instance Eq (Var U env a) where
--   VarU i == VarU j = i == j

-- instance Eq (Var S env a) where
--   VZ == VZ = True
--   VZ == (VS _) = False
--   (VS _) == VZ = False
--   (VS n) == (VS m) = n == m

-- extendEnv' :: (EnvImpl rep, Shiftable rep t) =>
--               Env' rep t env -> t env a ->
--               (Env' rep t (a : env), Var rep (a : env) a, VarT rep env (a : env))
-- extendEnv' env v =
--   let (env', r', vt') = extendEnv env v
--   in (mapEnv (shift vt') env', r', vt')

-- mapEnv :: (EnvImpl rep) =>
--           (forall a. t use a -> t' use' a) -> Env rep t use def -> Env rep t' use' def
-- mapEnv f = runIdentity . traverseEnvWithVar (const (Identity . f))

-- zipWithEnv :: EnvImpl rep =>
--               (forall a. t use a -> t' use' a -> t'' use'' a) ->
--               Env rep t use def -> Env rep t' use' def -> Env rep t'' use'' def
-- zipWithEnv f e1 e2 = runIdentity $ zipWithA (\x y -> Identity (f x y)) e1 e2

foldEnvWithVar ::
  (EnvImpl rep, Monoid m) =>
  (forall a. Var rep def a -> f a -> m) ->
  Env rep f def ->
  m
foldEnvWithVar f = getConst . traverseWithVar (\v e -> Const (f v e))

foldEnv :: (EnvImpl rep, Monoid m) => (forall a. f a -> m) -> Env rep f def -> m
foldEnv f = foldEnvWithVar (const f)

foldrEnv :: (EnvImpl rep) => (forall a. f a -> b -> b) -> b -> Env rep f def -> b
foldrEnv f = flip $ appEndo . foldEnv (Endo . f)

foldrEnvWithVar :: (EnvImpl rep) => (forall a. Var rep def a -> f a -> b -> b) -> b -> Env rep f def -> b
foldrEnvWithVar f = flip $ appEndo . foldEnvWithVar (\k x -> Endo (f k x))

pprEnv :: forall rep d f def. (EnvImpl rep, DocLike d) => (forall a. String -> f a -> d) -> Env rep f def -> d
pprEnv pprBody = fromMaybe empty . foldrEnvWithVar h Nothing
  where
    h :: forall env a. Var rep env a -> f a -> Maybe d -> Maybe d
    h v body r =
      let rd = align (pprBody (showVar v) body)
       in Just $ case r of
            Nothing -> rd
            Just d -> d $$ rd

--   -- foldrEnvWithVar (\v body r -> r $$ prefix <> text (showVar v) <+> text "=" <+> align (pprBody prefix body))
--   --                 empty
