{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-|
A file that contains manipulation of environments.
The file intentially uses some unsafe features in Haskell. 
-}

module Text.FliPpr.Internal.Env where

import Prelude hiding (id, (.))

import Control.Category
import Control.Applicative (Const(..))

import Data.Maybe (fromJust, fromMaybe)
import Data.Typeable ((:~:)(..), Proxy(..))
import Data.Monoid (Endo(..))
import Data.Kind 
import Data.IntMap (IntMap)
import Data.Functor.Identity (Identity(..))
import qualified Data.IntMap as IM

import Text.FliPpr.Doc 

import Unsafe.Coerce 


type Env' i t env = Env i t env env 

{- Environments that can be mutually recursive -}
newtype VarT d env env' = VarT { runVarT :: forall a. Var d env a -> Var d env' a }

class Shiftable d t where
  shift :: VarT d env env' -> t env a -> t env' a

instance Shiftable d (Var d) where
  shift = runVarT 


class DeBruijnIndex v where
  vz :: v (a : env) a
  vs :: v env a -> v (b : env) a

instance DeBruijnIndex (Var U) where
  vz = VarU 0
  vs (VarU i) = VarU (i+1)

instance DeBruijnIndex (Var S) where
  vz = VZ
  vs = VS 

instance Category (VarT d) where
  id = VarT id
  VarT f . VarT g = VarT (f . g) 

class EnvImpl i where
  data Var i :: [Type] -> Type -> Type 
  data Env i :: ([Type] -> Type -> Type) -> [Type] -> [Type] -> Type 
  data Rep i :: [Type] -> Type 

  showVar :: Var i env a -> String
  eqVar :: Var i env a -> Var i env b -> Maybe (a :~: b) 

  lookupEnv :: Var i def a -> Env i t use def -> t use a

  modifyEnv :: Var i def a -> (t use a -> t use a) -> Env i t use def -> Env i t use def
  modifyEnv x f env =
    let res = lookupEnv x env
    in updateEnv x (f res) env 

  updateEnv :: Var i def a -> t use a -> Env i t use def -> Env i t use def
  updateEnv x v = modifyEnv x (const v)
  
  traverseEnvWithVar ::
    Applicative f =>
    (forall a. Var i def a -> t use a -> f (t' use' a)) -> Env i t use def -> f (Env i t' use' def)


  zipWithA :: Applicative f =>
              (forall a. t use a -> t' use' a -> f (t'' use'' a)) ->
              Env i t use def -> Env i t' use' def -> f (Env i t'' use'' def)

  emptyEnv  :: Env i t use '[]
  extendEnv :: Env i t use def -> t use a -> (Env i t use (a : def), Var i (a : def) a, VarT i def (a : def))

  repOf :: Env i t use env -> Rep i env 

  -- env' must be bigger than or equal to env 
  embedVar :: Rep i env -> Rep i env' -> Var i env a -> Var i env' a

data U -- Unsafe

data Untype = forall a. Untype a

unsafeCast :: Untype -> a
unsafeCast (Untype a) = unsafeCoerce a 

instance EnvImpl U where
  newtype Var U env a   = VarU Int

  data Env U t env env' = EnvU !Int (IntMap Untype)
    -- ith var corresponds to (k-i)th index.
  newtype Rep U env        = RepU Int

  showVar (VarU n) = show n 
  eqVar (VarU n) (VarU m) =
    if n == m then
      unsafeCoerce (Just Refl)
    else
      Nothing 
      

  lookupEnv (VarU n) (EnvU k m) = unsafeCast (fromJust $ IM.lookup (k-n) m)
  modifyEnv (VarU n) f (EnvU k m) = EnvU k (IM.adjust (Untype . f . unsafeCast) (k-n) m)

  traverseEnvWithVar f (EnvU k m) = EnvU k <$> IM.traverseWithKey (\i x -> Untype <$> f (VarU (k-i)) (unsafeCast x)) m 

  zipWithA f (EnvU k m1) (EnvU _ m2) =
    EnvU k <$> sequenceA (IM.unionWith (\x y -> fmap Untype $ f <$> (unsafeCast <$> x) <*> (unsafeCast <$> y)) (fmap pure m1) (fmap pure m2))

  emptyEnv  = EnvU (-1) IM.empty
  extendEnv (EnvU k m) v = (EnvU (k+1) (IM.insert (k+1) (Untype v) m), VarU 0, VarT f)
    where
      f (VarU n) = VarU (n+1) 
  
  repOf (EnvU k _) = RepU k

  embedVar (RepU k) (RepU k') (VarU i) = VarU (i + (k' - k))


data M 
data S -- safe(r)

instance EnvImpl S where
  data Var S env a where
    VZ :: Var S (a : env) a
    VS :: Var S env a -> Var S (b : env) a

  data Env S t use def where
    EEnd    :: Env S t use '[]
    EExtend :: Env S t use def -> t use a -> Env S t use (a : def)

  data Rep S env where
    REnd    :: Rep S '[]
    RExtend :: Rep S env -> Proxy a -> Rep S (a : env) 

  eqVar VZ VZ         = Just Refl
  eqVar (VS n) (VS m) = eqVar n m
  eqVar _      _      = Nothing 

  showVar = show . go
    where
      go :: Var S env a -> Int 
      go VZ     = 0
      go (VS n) = 1 + go n 
      
  lookupEnv VZ     (EExtend _ v) = v
  lookupEnv (VS n) (EExtend e _) = lookupEnv n e 

  modifyEnv VZ     f (EExtend e v) = EExtend e (f v)
  modifyEnv (VS n) f (EExtend e v) = EExtend (modifyEnv n f e) v 

  traverseEnvWithVar _ EEnd          = pure EEnd
  traverseEnvWithVar f (EExtend e v) = go f e v (VarT id)
    where
      go :: Applicative f =>
            (forall a. Var S env a -> t use a -> f (t' use' a)) ->
            Env S t use def -> t use a -> VarT S (a : def) env -> f (Env S t' use' (a : def))
      go f EEnd t sh = EExtend EEnd <$> f (runVarT sh VZ) t
      go f (EExtend e t') t sh =
        EExtend <$> go f e t' (sh . VarT VS) <*> f (runVarT sh VZ) t 
      
  zipWithA _ EEnd EEnd = pure EEnd
  zipWithA f (EExtend e v) (EExtend e' v') =
    EExtend <$> zipWithA f e e' <*> f v v' 


  emptyEnv = EEnd
  extendEnv e v = (EExtend e v, VZ, VarT VS)

  repOf EEnd          = REnd
  repOf (EExtend e _) = RExtend (repOf e) Proxy

  -- embedVar (RExtend REnd _) (RExtend REnd _) VZ     = unsafeCoerce VZ 
  -- embedVar (RExtend REnd v) (RExtend e _)    VZ     = VS (embedVar (RExtend REnd v) e VZ)
  -- embedVar (RExtend e _)    (RExtend e' _)   (VS k) = VS (embedVar e e' k)
  embedVar r1 r2 n =
    case requal r1 r2 of
      Just Refl -> n
      _         ->
        case r2 of
          REnd -> error "Error: embedVar: violated assumption."
          RExtend r2' _ -> VS (embedVar r1 r2' n)
--   embedVar _                _                _      = error "Error: embedVar: violated assumption."
    where
      requal :: Rep S env -> Rep S env' -> Maybe (env :~: env')
      requal REnd REnd = Just Refl
      requal (RExtend e _) (RExtend e' _) =
        case requal e e' of
          Just Refl -> Just (unsafeCoerce Refl)
          Nothing   -> Nothing
      requal _ _ = Nothing 



instance Eq (Var U env a) where
  VarU i == VarU j = i == j

instance Eq (Var S env a) where
  VZ == VZ = True
  VZ == (VS _) = False
  (VS _) == VZ = False
  (VS n) == (VS m) = n == m 

extendEnv' :: (EnvImpl rep, Shiftable rep t) =>
              Env' rep t env -> t env a ->
              (Env' rep t (a : env), Var rep (a : env) a, VarT rep env (a : env))
extendEnv' env v =
  let (env', r', vt') = extendEnv env v
  in (mapEnv (shift vt') env', r', vt')

mapEnv :: (EnvImpl rep) =>
          (forall a. t use a -> t' use' a) -> Env rep t use def -> Env rep t' use' def
mapEnv f = runIdentity . traverseEnvWithVar (const (Identity . f)) 

foldEnvWithVar :: (EnvImpl rep, Monoid m) =>
                  (forall a. Var rep def a -> t use a -> m) ->
                  Env rep t use def -> m
foldEnvWithVar f = getConst . traverseEnvWithVar (\v e -> Const (f v e))

foldEnv :: (EnvImpl rep, Monoid m) =>
           (forall a. t use a -> m) -> Env rep t use def -> m
foldEnv f = foldEnvWithVar (const f) 

foldrEnv :: (EnvImpl rep) =>
            (forall a. t use a -> b -> b) -> b -> Env rep t use def -> b
foldrEnv f = flip $ appEndo . foldEnv (Endo . f) 


foldrEnvWithVar :: (EnvImpl rep) =>
                   (forall a. Var rep def a -> t use a -> b -> b) -> b -> Env rep t use def -> b
foldrEnvWithVar f = flip $ appEndo . foldEnvWithVar (\k x -> Endo (f k x))                   

pprEnv :: (EnvImpl rep, DocLike d) => (forall a. d -> t use a -> d) -> d -> Env rep t use def -> d
pprEnv pprBody prefix = fromMaybe empty .
  foldrEnvWithVar (\v body r ->                     
                     let rd = prefix <> text (showVar v) <+> text "=" <+> align (pprBody prefix body)
                     in Just $ case r of
                          Nothing -> rd
                          Just  d -> d $$ rd) Nothing
  
  -- foldrEnvWithVar (\v body r -> r $$ prefix <> text (showVar v) <+> text "=" <+> align (pprBody prefix body))
  --                 empty 
