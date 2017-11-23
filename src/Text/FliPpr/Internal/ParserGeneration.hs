{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# LANGUAGE GADTs #-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}

{-# LANGUAGE ScopedTypeVariables #-}

module Text.FliPpr.Internal.ParserGeneration where

import Data.Typeable 
import Data.Kind 

import Text.FliPpr.Internal.Type
import Text.FliPpr.Internal.Parsing 
import Data.STRef 
import Control.Applicative (Alternative, (<|>), liftA2)

import qualified Text.FliPpr.Doc as D 

import Unsafe.Coerce 

data Dynamic = forall a. (Typeable a, Eq a) => Dynamic a

checkEqT :: (Typeable a, Typeable b) => a -> b -> Maybe (a :~: b)
checkEqT _ _ = eqT 

instance Eq Dynamic where
  Dynamic a == Dynamic b =
    case checkEqT a b of
      Just Refl -> a == b
      Nothing   -> False 

toDyn :: (Eq a, Typeable a) => a -> Dynamic
toDyn a = Dynamic a

fromDynamic :: (Eq a, Typeable a) => Dynamic -> Maybe a
fromDynamic (Dynamic a) = cast a 


data Rep (r :: [Type]) where
  RepE   :: Int -> Rep '[]
  RepExt :: Int -> Rep r -> Proxy a -> Rep (a ': r) 

rlen :: Rep r -> Int
rlen (RepE n)       = n
rlen (RepExt n _ _) = n 

extend :: Rep r -> Proxy a -> Rep (a ': r)
extend r p = RepExt (rlen r + 1) r p 

-- phantom type 
type Env (r :: [Type]) = EnvImpl 

data EnvImpl = EnvEmp
             | EnvUndet 
             | EnvExt (Maybe Dynamic) EnvImpl

data Err a = Ok a | Fail D.Doc

instance Functor Err where
  fmap f (Ok a)   = Ok (f a)
  fmap f (Fail d) = Fail d

instance Applicative Err where
  pure = return
  Fail d <*> Ok _    = Fail d
  Fail d <*> Fail d' = Fail (d D.$$ d')
  Ok   f <*> Fail d  = Fail d
  Ok   f <*> Ok a    = Ok (f a)

instance Monad Err where
  return = Ok
  Fail d >>= f = Fail d
  Ok a >>= f   = f a 

  fail = Fail . D.text 

err :: D.Doc -> Err a 
err = Fail 
  
newtype PArg a   = PArg { unPArg :: forall r. Rep r -> Int }
newtype PExp p t = PExp { unPExp :: forall r. Rep r -> p (Err (Result r t)) }

data Result env t where
  RD :: Env env -> Result env D
  RF :: Result (a ': env) t -> Result env (a :~> t)

mapEnv :: (Env env -> Err (Env env')) -> Result env t -> Err (Result env' t)
mapEnv k (RD e) = RD <$> k e
mapEnv k (RF m) = RF <$> mapEnv (\(EnvExt a e) -> k e >>= \e' -> return (EnvExt a e')) m


insertEnv :: In a => Int -> Maybe a -> Env t -> Err (Env t)
insertEnv k = go k 
  where
    go :: In a => Int -> Maybe a -> Env t -> Err (Env t)
    go n a EnvEmp        = err $ D.text ("No index: " ++ show k)
    go 0 a (EnvExt b r)  = do
      a' <- checkEq a (fromDynamic =<< b)
      return $ EnvExt (fmap toDyn a') r
      where
        checkEq Nothing  b        = return b
        checkEq (Just a) Nothing  = return (Just a)
        checkEq (Just a) (Just b) =
          if a == b then
            return (Just a)
          else
            err $ D.text ("the same variable updated differently")
        
    go n a (EnvExt b r) = EnvExt b <$> go (n-1) a r
    go n a EnvUndet     = EnvExt Nothing <$> go (n-1) a EnvUndet 

-- type family Result env (t :: FType)
-- type instance Result env D        = env
-- type instance Result env (a :~> r) = Result env r :> a

-- data Result env t where
--   RD :: TEnv env -> Result env D
--   RF :: Int -> Result env r -> Maybe a -> Result env (a :~> r)


choice :: Alternative p => PExp p r -> PExp p r -> PExp p r 
choice p q = PExp $ \tenv -> unPExp p tenv <|> unPExp q tenv 
      
fromP :: Functor p => p a -> PExp p D
fromP x = PExp $ \_ -> (return $ RD EnvUndet) <$ x 

instance ParserLike p => FliPprE PArg (PExp p) where
  app :: forall a t. In a => PExp p (a :~> t) -> PArg a -> PExp p t 
  app (PExp f) (PArg n) =
    PExp $ \tenv -> fmap (>>= (\k -> appSem k (n tenv))) (f tenv) 
    where
      appSem :: In a => Result r (a :~> t) -> Int -> Err (Result r t) 
      appSem (RF m) k =
        mapEnv (\(EnvExt d env) -> insertEnv k (fromDynamic =<< d :: Maybe a) env) m


  arg :: forall a t. In a => (PArg a -> PExp p t) -> PExp p (a :~> t)
  arg f = PExp $ \tenv ->
                   let tenva = extend tenv (Proxy :: Proxy a)
                       aa    = PArg $ \tenv' -> rlen tenv' - rlen tenva 
                   in fmap RF <$> unPExp (f aa) tenva

  ffix :: (PExp p t -> PExp p t) -> PExp p t
  ffix f = PExp $ \tenv ->
                    pfix (\p -> let p' = PExp $ \tenv' -> fmap (>>= mapEnv (return . embed tenv tenv')) p 
                                in unPExp (f p') tenv)
    where
      embed :: Rep env -> Rep env' -> Env env -> Env env'
      embed tenv tenv' = go (rlen tenv' - rlen tenv)
        where
          go 0 r = r
          go n r = EnvExt Nothing r 


  unpair :: forall a b r.
            (In a, In b) => PArg (a,b) -> (PArg a -> PArg b -> PExp p r) -> PExp p r
  unpair inp f = PExp $ \tenv ->
                          let tenva = extend tenv  (Proxy :: Proxy a) 
                              tenvb = extend tenva (Proxy :: Proxy b)
                              ia    = PArg $ \tenv' -> rlen tenv' - rlen tenva
                              ib    = PArg $ \tenv' -> rlen tenv' - rlen tenvb
                          in fmap (>>= mapEnv (\(EnvExt bv (EnvExt av e)) ->
                                                 let ab = liftA2 (,) (fromDynamic =<< av :: Maybe a)
                                                                     (fromDynamic =<< bv :: Maybe b)
                                                     k  = unPArg inp tenv 
                                                 in insertEnv k ab e)) $ unPExp (f ia ib) tenvb

  case_ inp [] = PExp $ \_ -> pfail ""
  case_ inp (Branch (PInv f finv) k : bs) =
    (branch inp (PInv f finv) k)
    `choice`
    (case_ inp bs)
    where
      branch :: (In a, In b) => PArg a -> (a <-> b) -> (PArg b -> PExp p r) -> PExp p r 
      branch inp (PInv f finv) k =
            (PExp $ \tenv ->
              let tenvb = extend tenv (Proxy :: Proxy b)
                  ib    = PArg $ \tenv' -> rlen tenv' - rlen tenvb
              in fmap (>>= mapEnv (\(EnvExt bv e) ->
                                      let av = refine (fromDynamic =<< bv) >>= finv
                                          k  = unPArg inp tenv
                                      in insertEnv k av e)) $ unPExp (k ib) tenvb)

      refine :: forall b. Typeable b => Maybe b -> Maybe b
      refine x =
        case eqT :: Maybe (b :~: ()) of
          Just Refl -> Just ()
          _         -> x


  ftext s = fromP $ ptext ""
  
  fcat f g = PExp $ \tenv -> (\x y -> liftA2 k x y >>= id) <$> unPExp f tenv <*> unPExp g tenv
    where
      k :: Result env D -> Result env D -> Err (Result env D)
      k (RD env) (RD env') = RD <$> merge env env'

      check :: Maybe Dynamic -> Maybe Dynamic -> Err (Maybe Dynamic)
      check Nothing b = return b
      check a Nothing = return a
      check (Just a) (Just b) =
        if a == b then return (Just a) else err $ D.text "Merge failed: update is consistent."


      merge :: Env t -> Env t -> Err (Env t)
      merge EnvUndet     b            = return b
      merge EnvEmp       EnvEmp       = return EnvEmp
      merge EnvEmp       EnvUndet     = return EnvEmp
      merge (EnvExt a r) (EnvExt b s) = do
        c <- check a b
        t <- merge r s
        return $ EnvExt c t
      merge (EnvExt a r) EnvUndet     = return (EnvExt a r)
      merge _            _            = error "Cannot happen."
      
        
  
  d1 <? d2 = choice d1 d2
  
  fempty = fromP $ ptext ""

  fspaces    = fromP pspaces
  fline      = fspaces
  flinebreak = fspaces

  falign     = id
  fgroup     = id
  fnest n    = id 
  
    
                                     
  
  
