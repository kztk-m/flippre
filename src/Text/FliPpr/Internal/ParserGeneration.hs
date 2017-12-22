{-# LANGUAGE PolyKinds #-}
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
import Data.Functor.Identity 

import Text.FliPpr.Internal.Type
import Text.FliPpr.Container2
import Text.FliPpr.Internal.CPS

import qualified Text.FliPpr.Internal.Grammar as G 
import Control.Applicative ((<|>), liftA2)

import qualified Text.FliPpr.Internal.PartialEnv as PE 
import qualified Text.FliPpr.Doc as D 

import qualified Control.Applicative as A (empty)

type PEImpl = PE.U 
type Rep = PE.Rep PEImpl
type Env = PE.Env PEImpl EqI
type Var = PE.Var PEImpl


data EqI a where
  EqI :: Eq a => a -> EqI a 


type GU = G.GrammarUC 

-- mergeEq :: Eq a -> a -> a -> Maybe a
-- mergeEq a b | a == b    = Just a
--             | otherwise = Nothing 


mergeEqI :: EqI a -> EqI a -> Maybe (EqI a)
mergeEqI (EqI a) (EqI b) | a == b    = Just (EqI a)
                         | otherwise = Nothing 

-- data Dynamic = forall a. (Typeable a, Eq a) => Dynamic a

-- checkEqT :: (Typeable a, Typeable b) => a -> b -> Maybe (a :~: b)
-- checkEqT _ _ = eqT 

-- instance Eq Dynamic where
--   Dynamic a == Dynamic b =
--     case checkEqT a b of
--       Just Refl -> a == b
--       Nothing   -> False 

-- toDyn :: (Eq a, Typeable a) => a -> Dynamic
-- toDyn a = Dynamic a

-- fromDynamic :: (Eq a, Typeable a) => Dynamic -> Maybe a
-- fromDynamic (Dynamic a) = cast a 


-- data Rep (r :: [Type]) where
--   RepE   :: Int -> Rep '[]
--   RepExt :: Int -> Rep r -> Proxy a -> Rep (a ': r) 

-- rlen :: Rep r -> Int
-- rlen (RepE n)       = n
-- rlen (RepExt n _ _) = n 

-- extend :: Rep r -> Proxy a -> Rep (a ': r)
-- extend r p = RepExt (rlen r + 1) r p 

-- -- phantom type 
-- type Env (r :: [Type]) = EnvImpl 

-- data EnvImpl = EnvEmp
--              | EnvUndet 
--              | EnvExt (Maybe Dynamic) EnvImpl

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
  
newtype PArg a = PArg { unPArg :: forall r. Rep r -> Var r a }
newtype PExp t = PExp { unPExp :: forall r. Rep r -> GU (Err (Result r t)) }

data Result env t where
  RD :: Env env -> Result env D
  RF :: Result (a ': env) t -> Result env (a :~> t)

-- data Result env t where
--   RD :: Env env -> Result env D
--   RF :: a -> Result env t -> Result env (a :~> t)

applySem :: GU (Err (Result r (a :~> t))) -> Var r a
            -> GU (Err (Result r t))
applySem g v = (>>= \res -> appSem res v) <$> g

appSem :: Result r (a :~> t) -> Var r a -> Err (Result r t) 
appSem (RF res) v =
  mapToEnvA (\env -> let (a,e) = PE.popEnv env
                     in tryUpdateEnv v a e) res

mapToEnvA :: Applicative f =>
             (Env env -> f (Env env')) ->  Result env t -> f (Result env' t)
mapToEnvA f (RD e) = RD <$> f e
mapToEnvA f (RF e) = RF <$> mapToEnvA (\env -> let (a,e) = PE.popEnv env
                                               in extEnv a <$> f e) e
  where    
    extEnv a e = case PE.extendEnv e a of
                   (e', _, _) -> e' 

mapToEnv :: (Env env -> Env env') -> Result env t -> Result env' t
mapToEnv f = runIdentity . (mapToEnvA (Identity . f))

tryUpdateEnv :: Var env a -> Maybe (EqI a) -> Env env -> Err (Env env)
tryUpdateEnv k Nothing  env = return env
tryUpdateEnv k (Just v) env =
  case PE.updateEnv mergeEqI k v env of
    Just env' -> return env'
    Nothing   -> err (D.text "The same variable is updated twice")

-- mapEnv :: (Env env -> Err (Env env')) -> Result env t -> Err (Result env' t)
-- mapEnv k (RD e) = RD <$> k e
-- mapEnv k (RF m) = RF <$> mapEnv (\(EnvExt a e) -> k e >>= \e' -> return (EnvExt a e')) m


-- insertEnv :: In a => Int -> Maybe a -> Env t -> Err (Env t)
-- insertEnv k = go k 
--   where
--     go :: In a => Int -> Maybe a -> Env t -> Err (Env t)
--     go n a EnvEmp        = err $ D.text ("No index: " ++ show k)
--     go 0 a (EnvExt b r)  = do
--       a' <- checkEq a (fromDynamic =<< b)
--       return $ EnvExt (fmap toDyn a') r
--       where
--         checkEq Nothing  b        = return b
--         checkEq (Just a) Nothing  = return (Just a)
--         checkEq (Just a) (Just b) =
--           if a == b then
--             return (Just a)
--           else
--             err $ D.text ("the same variable updated differently")
        
--     go n a (EnvExt b r) = EnvExt b <$> go (n-1) a r
--     go n a EnvUndet     = EnvExt Nothing <$> go (n-1) a EnvUndet 

-- type family Result env (t :: FType)
-- type instance Result env D        = env
-- type instance Result env (a :~> r) = Result env r :> a

-- data Result env t where
--   RD :: TEnv env -> Result env D
--   RF :: Int -> Result env r -> Maybe a -> Result env (a :~> r)


choice :: PExp r -> PExp r -> PExp r 
choice p q = PExp $ \tenv -> unPExp p tenv <|> unPExp q tenv
      
fromP :: GU a -> PExp D
fromP x = PExp $ \_ -> (return $ RD PE.undeterminedEnv) <$ x 

instance FliPprCPre PArg PExp where
  fapp :: forall a t. In a => PExp (a :~> t) -> PArg a -> PExp t 
  fapp (PExp f) (PArg n) = 
    PExp $ \tenv -> applySem (f tenv) (n tenv)

  farg :: forall a t. In a => (PArg a -> PExp t) -> PExp (a :~> t)
  farg f = PExp $ \tenv ->
    case PE.extendRep tenv Proxy of
      (tenva, va, vt) ->
        let arg = PArg $ \tenv' -> PE.embedVar tenva tenv' va
        in fmap RF <$> unPExp (f arg) tenva 
             
  funpair :: forall a b r.
            (In a, In b) => PArg (a,b) -> (PArg a -> PArg b -> PExp r) -> PExp r
  funpair inp f = PExp $ \tenv ->
    let (tenva, va, _) = PE.extendRep tenv  Proxy
        (tenvb, vb, _) = PE.extendRep tenva Proxy
        argA           = PArg $ \tenv' -> PE.embedVar tenva tenv' va
        argB           = PArg $ \tenv' -> PE.embedVar tenvb tenv' vb
    in (>>= updateP (unPArg inp tenv)) <$> unPExp (f argA argB) tenvb
    where
      updateP :: Var env (a,b) -> Result (b : a : env) r -> Err (Result env r)
      updateP v = mapToEnvA $
                \eab -> let (b, ea) = PE.popEnv eab
                            (a, e)  = PE.popEnv ea
                        in tryUpdateEnv v (liftA2 pair a b) e

      pair :: (EqI a) -> (EqI b) -> EqI (a,b)
      pair (EqI a) (EqI b) = EqI (a,b) 
    
    -- let tenva = extend tenv  (Proxy :: Proxy a) 
    --     tenvb = extend tenva (Proxy :: Proxy b)
    --     ia    = PArg $ \tenv' -> rlen tenv' - rlen tenva
    --     ib    = PArg $ \tenv' -> rlen tenv' - rlen tenvb
    -- in fmap (>>= mapEnv (\(EnvExt bv (EnvExt av e)) ->
    --                      let ab = liftA2 (,) (fromDynamic =<< av :: Maybe a)
    --                               (fromDynamic =<< bv :: Maybe b)
    --                          k  = unPArg inp tenv 
    --                      in insertEnv k ab e))
    --    $ unPExp (f ia ib) tenvb

  fcase inp [] = PExp $ \_ -> A.empty 
  fcase inp (Branch (PInv s f finv) k : bs) =
    (branch inp (PInv s f finv) k)
    `choice`
    (fcase inp bs)
    where
      branch :: (In a, In b) => PArg a -> (a <-> b) -> (PArg b -> PExp r) -> PExp r 
      branch inp (PInv _ f finv) k =
        PExp $ \tenv ->
        let (tenvb, vb, _) = PE.extendRep tenv Proxy
            argB  = PArg $ \tenv' -> PE.embedVar tenvb tenv' vb
        in (>>= updateB finv (unPArg inp tenv)) <$> unPExp (k argB) tenvb

      updateB :: (In a, In b) =>
                 (b -> Maybe a) -> Var env a -> Result (b : env) r -> Err (Result env r) 
      updateB finv v = mapToEnvA $ \eb ->
        let (b, e) = PE.popEnv eb
            a      = fmap EqI $ refine b >>= \b' -> case b' of
                                                      EqI bb -> finv bb
        in tryUpdateEnv v a e 
        -- let tenvb = extend tenv (Proxy :: Proxy b)
        --     ib    = PArg $ \tenv' -> rlen tenv' - rlen tenvb
        -- in  (>>= mapEnv (\(EnvExt bv e) ->
        --                     let av = refine (fromDynamic =<< bv) >>= finv
        --                         k  = unPArg inp tenv
        --                     in insertEnv k av e)) <$> unPExp (k ib) tenvb

      refine :: forall b. Typeable b => Maybe (EqI b) -> Maybe (EqI b)
      refine x =
        case eqT :: Maybe (b :~: ()) of
          Just Refl -> Just (EqI ())
          _         -> x


  ftext s = fromP $ G.gtext s
  
  fcat f g = PExp $ \tenv -> 
    let p = unPExp f tenv
        q = unPExp g tenv 
    in (\x y -> liftA2 k x y >>= id) <$> p <*> q 
    where
      k :: Result env D -> Result env D -> Err (Result env D)
      k (RD env) (RD env') = RD <$> merge env env'

      merge e e' = case PE.mergeEnv mergeEqI e e' of
                     Nothing  -> err $ D.text"Merge failed: update is consistent."
                     Just env -> return env 


  
  fbchoice d1 d2 = choice d1 d2
  
  fempty = fromP $ G.gtext ""

  fspace     = fromP G.gspace 
  fspaces    = fromP G.gspaces
  
  fline      = fspaces
  flinebreak = fspaces

  falign     = id
  fgroup     = id
  fnest n    = id 


instance FliPprC PArg PExp where
  ffix :: Container2 k =>
          k (Rec k PExp) -> C PExp (k PExp)
  ffix defs =
    CPS $ \k -> PExp $ \(tenv :: Rep env) ->
     let toPExp :: forall a. (GU :.: (Err :.: Result env)) a -> PExp a 
         toPExp   = makeArg tenv
         fromPExp :: forall a. PExp a -> (GU :.: (Err :.: Result env)) a 
         fromPExp = run tenv 
     in unlift $
         runCPS (G.gfixGen (fmap2 (adjustRec2 fromPExp toPExp) defs))
                (fromPExp . k . fmap2 toPExp) 
    
    -- unlift $ runCPS
    --  (G.gfixGen
    --    (fmap2 (\r -> Rec $ \x -> run tenv $ runRec r (fmap2 (makeArg tenv) x)) defs))
    --  (\xs -> run tenv $ k (fmap2 (makeArg tenv) xs))
    where
      run :: Rep env -> PExp a -> (GU :.: (Err :.: Result env)) a
      run tenv p = lift (unPExp p tenv)

      makeArg :: Rep env -> (GU :.: (Err :.: Result env)) a -> PExp a
      makeArg tenv g' =
        let g = unlift g'
        in PExp $ \tenv' -> (fmap $ mapToEnv (PE.embedEnv tenv tenv')) <$> g
    
      lift :: forall f g h (a :: k). Functor f => f (g (h a)) -> (f :.: (g :.: h)) a
      lift x = Comp (fmap Comp x)

      unlift :: forall f g h (a :: k). Functor f => (f :.: (g :.: h)) a -> f (g (h a))
      unlift x = fmap getComp (getComp x)

{-  
  ffix :: TypeList ts =>
          (Apps PExp ts -> Apps PExp ts) ->
          (Apps PExp ts -> PExp r) -> PExp r
  ffix f k = PExp $ \tenv ->
    unlift $ G.gfixnp (\gs -> mapApps (run tenv) $ f $ mapApps (makeArg tenv) gs)
                      (\gs -> run tenv $ k $ mapApps (makeArg tenv) gs)
    where     
      run :: Rep env -> PExp a -> (GU :.: (Err :.: Result env)) a
      run tenv p = lift (unPExp p tenv)

      makeArg :: Rep env -> (GU :.: (Err :.: Result env)) a -> PExp a
      makeArg tenv g' =
        let g = unlift g'
        in PExp $ \tenv' -> (fmap $ mapToEnv (PE.embedEnv tenv tenv')) <$> g

      lift :: forall f g h (a :: k). Functor f => f (g (h a)) -> (f :.: (g :.: h)) a
      lift x = Comp (fmap Comp x)

      unlift :: forall f g h (a :: k). Functor f => (f :.: (g :.: h)) a -> f (g (h a))
      unlift x = fmap getComp (getComp x)
-}

parsingModeMono :: In a => PExp (a :~> D) -> G.Grammar (Err a)
parsingModeMono e =
  G.reduce $ G.finalize $ k <$> unPExp e (PE.emptyRep)
  where
    k :: In a => Err (Result '[] (a :~> D)) -> Err a
    k (Fail s) = err $ D.text "Inverse computation fails: " D.</> s
    k (Ok a)   =
      case a of
        RF (RD e) ->
          let (a, _) = PE.popEnv e
          in case a of
            Just (EqI a) -> return a
            Nothing      -> err $ D.text "Input is unused in evaluation."

parsingMode :: In a => FliPpr (a :~> D) -> G.Grammar (Err a)
parsingMode (FliPpr e) = parsingModeMono e 
                            
-- parsingMode :: (In a, ParserFix p) => FliPpr (a :~> D) -> p (Err a)
-- parsingMode (FliPpr e) = 
--   k <$> unPExp e (RepE 0)
--     where
--       k :: In a => Err (Result '[] (a :~> D)) -> Err a
--       k (Fail s) = err $ D.text "Inverse computation fails: " D.</> s
--       k (Ok  a)  =
--         case a of
--           RF (RD (EnvExt c EnvEmp)) ->
--             case c of
--               Just a  -> maybe undefined return $ fromDynamic a
--               Nothing -> err $ D.text "Input is unused in evaluation." 
    

