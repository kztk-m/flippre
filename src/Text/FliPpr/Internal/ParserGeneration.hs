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

import Control.Monad (join) 
import Control.Applicative ((<|>), liftA2)
import qualified Control.Applicative as A (empty)

import Control.Monad.Reader

import Text.FliPpr.Internal.Type

import qualified Text.FliPpr.Internal.GrammarST as G 
import qualified Text.FliPpr.Internal.PartialEnv as PE 
import qualified Text.FliPpr.Doc as D 

import Text.FliPpr.Internal.Ref

type PEImpl = PE.U 
type Rep = PE.Rep PEImpl
type Env = PE.Env PEImpl EqI
type Var = PE.Var PEImpl


data EqI a where
  EqI :: Eq a => a -> EqI a 

type GU s = G.OpenGrammar s G.ExChar 

mergeEqI :: EqI a -> EqI a -> Maybe (EqI a)
mergeEqI (EqI a) (EqI b) | a == b    = Just (EqI a)
                         | otherwise = Nothing 

data Err a = Ok a | Fail D.Doc

instance Functor Err where
  fmap f (Ok a)   = Ok (f a)
  fmap _ (Fail d) = Fail d

instance Applicative Err where
  pure = return
  Fail d <*> Ok _    = Fail d
  Fail d <*> Fail d' = Fail (d D.$$ d')
  Ok   _ <*> Fail d  = Fail d
  Ok   f <*> Ok a    = Ok (f a)

instance Monad Err where
  return = Ok
  Fail d >>= _ = Fail d
  Ok a >>= f   = f a 

  fail = Fail . D.text 

err :: D.Doc -> Err a 
err = Fail 
  
newtype PArg a   = PArg { unPArg :: forall r. Rep r -> Var r a }
newtype PExp s t = PExp { unPExp :: forall r. Rep r -> GU s (Err (Result r t)) }

data Result env t where
  RD :: Env env -> Result env D
  RF :: Result (a ': env) t -> Result env (a :~> t)

applySem :: GU s (Err (Result r (a :~> t))) -> Var r a
            -> GU s (Err (Result r t))
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
mapToEnv f = runIdentity . mapToEnvA (Identity . f)

tryUpdateEnv :: Var env a -> Maybe (EqI a) -> Env env -> Err (Env env)
tryUpdateEnv _ Nothing  env = return env
tryUpdateEnv k (Just v) env =
  case PE.updateEnv mergeEqI k v env of
    Just env' -> return env'
    Nothing   -> err (D.text "The same variable is updated twice")


choice :: PExp s D -> PExp s D -> PExp s D
choice p q = PExp $ \tenv -> unPExp p tenv <|> unPExp q tenv

choiceGen :: PExp s r -> PExp s r -> PExp s r
choiceGen p q = PExp $ \tenv -> unPExp p tenv <|> unPExp q tenv 
                                                                   
fromP :: GU s a -> PExp s D
fromP x = PExp $ \_ -> G.constantResult (return $ RD PE.undeterminedEnv) x
  -- return (RD PE.undeterminedEnv) <$ x 

instance FliPprE PArg (PExp s) where
  fapp :: forall a t. In a => PExp s (a :~> t) -> PArg a -> PExp s t 
  fapp (PExp f) (PArg n) = 
    PExp $ \tenv -> applySem (f tenv) (n tenv)

  farg :: forall a t. In a => (PArg a -> PExp s t) -> PExp s (a :~> t)
  farg f = PExp $ \tenv ->
    case PE.extendRep tenv Proxy of
      (tenva, va, _vt) ->
        let arg = PArg $ \tenv' -> PE.embedVar tenva tenv' va
        in fmap RF <$> unPExp (f arg) tenva 
             
  funpair :: forall a b r.
            (In a, In b) => PArg (a,b) -> (PArg a -> PArg b -> PExp s r) -> PExp s r
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

      pair :: EqI a -> EqI b -> EqI (a,b)
      pair (EqI a) (EqI b) = EqI (a,b) 
    

  fcase _   [] = PExp $ const A.empty 
  fcase inp (Branch (PInv s f finv) k : bs) =
    branch inp (PInv s f finv) k
    `choiceGen`
    fcase inp bs
    where
      branch :: (In a, In b) => PArg a -> (a <-> b) -> (PArg b -> PExp s r) -> PExp s r 
      branch inp (PInv _ _ finv) k =
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

      refine :: forall b. Typeable b => Maybe (EqI b) -> Maybe (EqI b)
      refine x =
        case eqT :: Maybe (b :~: ()) of
          Just Refl -> Just (EqI ())
          _         -> x


  ftext s = fromP $ G.text s
  
  fcat f g = PExp $ \tenv -> 
    let p = unPExp f tenv
        q = unPExp g tenv 
    in (\x y -> join (liftA2 k x y)) <$> p <*> q 
    where
      k :: Result env D -> Result env D -> Err (Result env D)
      k (RD env) (RD env') = RD <$> merge env env'

      merge e e' = case PE.mergeEnv mergeEqI e e' of
                     Nothing  -> err $ D.text "Merge failed: update is consistent."
                     Just env -> return env 


  
  fbchoice = choice 
  
  fempty = fromP $ G.text ""

  fspace     = fromP G.space 
  fspaces    = fromP G.spaces

  fnespaces' = fromP G.spaces 
  
  fline      = fromP $ G.space <* G.spaces
  fline'     = fspaces 
  flinebreak = fspaces

  falign     = id
  fgroup     = id
  fnest _    = id 


newtype PM s a = PM { runPM :: forall env. ReaderT (Rep env) (RefM s) a } 

instance Functor (PM s) where
  fmap f (PM m) = PM (fmap f m)

instance Applicative (PM s) where
  pure a = PM (pure a)
  PM f <*> PM a = PM (f <*> a) 

instance Monad (PM s) where
  return = pure
  PM m >>= f = PM $ m >>= runPM . f

instance MonadFix (PM s) where
  mfix f = PM (mfix (runPM . f))


data SomeRep = forall env. SomeRep (Rep env)
  
askRep :: PM s SomeRep 
askRep = PM $ SomeRep <$> ask 

instance FliPprD (PM s) PArg (PExp s) where
  fshare (PExp e) = do 
    SomeRep tenv <- askRep
    g <- PM $ lift $ G.share (e tenv)
    return $ PExp $ \tenv' -> fmap (fmap (mapToEnv $ PE.embedEnv tenv tenv')) g 


  flocal m = PExp $ \tenv ->
    G.OpenG $ do
      e <- runReaderT (runPM m) tenv
      r <- G.runOpenG $ unPExp e tenv
      return r 

-- instance FliPprE PArg PExp where
--   ffix :: Container2 k =>
--           k (Rec k PExp) -> C PExp (k PExp)
--   ffix defs =
--     CPS $ \k -> PExp $ \(tenv :: Rep env) ->
--      let toPExp :: forall a. (GU :.: (Err :.: Result env)) a -> PExp a 
--          toPExp   = makeArg tenv
--          fromPExp :: forall a. PExp a -> (GU :.: (Err :.: Result env)) a 
--          fromPExp = run tenv 
--      in unlift $
--          runCPS (G.gfixGen (fmap2 (adjustRec2 fromPExp toPExp) defs))
--                 (fromPExp . k . fmap2 toPExp) 
    
--     -- unlift $ runCPS
--     --  (G.gfixGen
--     --    (fmap2 (\r -> Rec $ \x -> run tenv $ runRec r (fmap2 (makeArg tenv) x)) defs))
--     --  (\xs -> run tenv $ k (fmap2 (makeArg tenv) xs))
--     where
--       run :: Rep env -> PExp a -> (GU :.: (Err :.: Result env)) a
--       run tenv p = lift (unPExp p tenv)

--       makeArg :: Rep env -> (GU :.: (Err :.: Result env)) a -> PExp a
--       makeArg tenv g' =
--         let g = unlift g'
--         in PExp $ \tenv' -> fmap (mapToEnv (PE.embedEnv tenv tenv')) <$> g
    
--       lift :: forall f g h (a :: k). Functor f => f (g (h a)) -> (f :.: (g :.: h)) a
--       lift x = Comp (fmap Comp x)

--       unlift :: forall f g h (a :: k). Functor f => (f :.: (g :.: h)) a -> f (g (h a))
--       unlift x = fmap getComp (getComp x)

--   flet :: PExp a -> C PExp (PExp a)
--   flet a = cps $ \k -> PExp $ \tenv -> 
--     runCPS (G.gshare (unPExp a tenv))
--            (\p -> unPExp (k (PExp $ \tenv' ->
--                             fmap (mapToEnv $ PE.embedEnv tenv tenv') <$> p))
--                   tenv) 

parsingModeMono :: In a => (forall s. PM s (PExp s (a :~> D))) -> G.Grammar G.ExChar (Err a)
parsingModeMono m = G.finalize $ do
  e <- runReaderT (runPM m) PE.emptyRep 
  return $ k <$> unPExp e PE.emptyRep 
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

parsingMode :: In a => FliPpr (a :~> D) -> G.Grammar G.ExChar (Err a)
parsingMode (FliPpr m) = parsingModeMono m
                            
