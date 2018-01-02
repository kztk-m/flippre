{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

{- |
Partial environment. Unlike @Env@, this module is for non-recursive environment
of which entry can be missing.
-}

module Text.FliPpr.Internal.PartialEnv where

import Data.Kind 
import Data.Typeable (Proxy, (:~:)(..))
import Control.Category

import Unsafe.Coerce 

newtype VarT i env env' = VarT { runVarT :: forall a. Var i env a -> Var i env' a}

instance Category (VarT i) where
  id = VarT Prelude.id
  VarT f . VarT g = VarT (f Prelude.. g) 



class PartialEnvImpl i where
  data Var i :: [Type] -> Type -> Type
  data Env i :: (Type -> Type) -> [Type] -> Type
  data Rep i :: [Type] -> Type


  lookupEnv :: Var i env a -> Env i t env -> Maybe (t a)
  updateEnv :: (forall a. t a -> t a -> Maybe (t a))
               -> Var i env a -> t a -> Env i t env -> Maybe (Env i t env)

  mergeEnv :: (forall a. t a -> t a -> Maybe (t a))
              -> Env i t env -> Env i t env -> Maybe (Env i t env)

  emptyEnv :: Env i t '[]
  undeterminedEnv :: Env i t env 

  extendEnv :: Env i t env -> Maybe (t a)
               -> (Env i t (a : env), Var i (a : env) a, VarT i env (a : env))

  emptyRep :: Rep i '[]
  isEmptyRep :: Rep i r -> Maybe (r :~: '[]) 
  
  extendRep :: Rep i env -> Proxy a ->
               (Rep i (a : env), Var i (a : env) a, VarT i env (a : env))

  popEnv :: Env i t (a : env) -> (Maybe (t a), Env i t env)  


  {-
    The following functions are meaningful only when
    env <= env' 
  -}
  
  embedVar :: Rep i env -> Rep i env' -> Var i env a -> Var i env' a
  embedEnv :: Rep i env -> Rep i env' -> Env i t env -> Env i t env' 

  
data U

data Untype = forall a. Untype a

unsafeCast :: Untype -> a
unsafeCast (Untype a) = unsafeCoerce a

data EnvImpl = EEmp
             | EUndet 
             | EExt (Maybe Untype) EnvImpl


instance PartialEnvImpl U where
  newtype Var U env a = VarU Int
  newtype Env U t a = EnvU EnvImpl 

  newtype Rep U env = RepU Int

  lookupEnv (VarU i) (EnvU es) = unsafeCast <$> go i es
    where
      go :: Int -> EnvImpl -> Maybe Untype
      go 0 (EExt v _) = v
      go n (EExt _ e) = go (n-1) e
      go _ _          = Nothing

  updateEnv mg (VarU i) v (EnvU es) = EnvU <$> go i v es
    where
      go 0 v (EExt Nothing e) = Just (EExt (Just (Untype v)) e)
      go 0 v (EExt (Just v') e)
        | Just r <- mg v (unsafeCast v') = Just (EExt (Just (Untype r)) e)
      go n v (EExt v' e) = EExt v' <$> go (n-1) v e
      go _ _ _           = Nothing

  mergeEnv mg (EnvU es) (EnvU es') = EnvU <$> go es es' 
    where
      go EEmp   EEmp   = return EEmp
      go e      EUndet = return e 
      go EUndet e      = return e
      go (EExt Nothing e) (EExt v' e') = 
        EExt v' <$> go e e'
      go (EExt v e) (EExt Nothing e') =
        EExt v <$> go e e'
      go (EExt (Just v) e) (EExt (Just v') e') = do
        e'' <- go e e'
        v'' <- mg (unsafeCast v) (unsafeCast v')
        return $ EExt (Just (Untype v'')) e''
      go _ _ = Nothing

  emptyEnv = EnvU EEmp
  undeterminedEnv = EnvU EUndet
  
  extendEnv (EnvU env) v = (EnvU (EExt (Untype <$> v) env),
                            VarU 0,
                            VarT (\(VarU i) -> VarU (i+1)))

  emptyRep = RepU 0
  isEmptyRep (RepU k) =
    if k == 0 then
      Just (unsafeCoerce Refl)
    else
      Nothing 
  
  extendRep (RepU k) _ =
    (RepU (k+1), VarU 0, VarT (\(VarU i) -> VarU (i+1)))
     

  popEnv (EnvU env) = let (v,e) = go env
                      in (unsafeCast <$> v, EnvU e)
    where
      go (EExt v e) = (v,e)
      go EUndet     = (Nothing, EUndet)
      go EEmp       = error "Cannot happen"
  
  embedVar (RepU k) (RepU k') (VarU i) = VarU (i + (k' - k))
  embedEnv (RepU k) (RepU k') (EnvU env) = EnvU (go (k'-k) env)
    where
      go 0 env = env
      go n env = EExt Nothing (go (n-1) env)
    
  
    
    

  
