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

{-# LANGUAGE RecursiveDo #-}

module Text.FliPpr.Internal.ParserGeneration where

import Data.Typeable 
import Data.Functor.Identity 

import Control.Monad (join) 
import Control.Applicative ((<|>), liftA2, many)
import qualified Control.Applicative as A (empty)

import Control.Monad.Reader

import Text.FliPpr.Internal.Type
import Text.FliPpr.Err 

import qualified Text.FliPpr.Internal.GrammarST as G 
import qualified Text.FliPpr.Internal.PartialEnv as PE 
import qualified Text.FliPpr.Doc as D 

import Text.FliPpr.Internal.Ref

import qualified Data.RangeSet.List as RS 

-- import Debug.Trace 

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
    Just env' -> -- trace (show $ pprEnv env D.<+> D.text "->" D.<+> D.align (pprEnv env')) $
                 return env'
    Nothing   -> err (D.text "The same variable is updated twice:"
                              D.$$ D.text "updating position" D.<+> pprVar k D.<+> D.text "in" D.<+> pprEnv env )
  where
    pprVar (PE.VarU i) = D.ppr i 

pprEnv :: Env env -> D.Doc 
pprEnv (PE.EnvU impl) = D.group $ D.text "<" D.<> go (0 :: Int) impl D.<> D.text ">"
  where
  go _ PE.EEmp   = D.empty
  go _ PE.EUndet = D.text "???"
  go n (PE.EExt b r) =
    (D.ppr n D.<> D.text ":" D.<> maybe (D.text "_") (const $ D.text "*") b) D.</> go (n+1) r 

choice :: PExp s D -> PExp s D -> PExp s D
choice p q = PExp $ \tenv -> unPExp p tenv <|> unPExp q tenv

choiceGen :: PExp s r -> PExp s r -> PExp s r
choiceGen p q = PExp $ \tenv -> unPExp p tenv <|> unPExp q tenv 
                                                                   
fromP :: GU s a -> PExp s D
fromP x = PExp $ \_ -> G.constantResult (return $ RD PE.undeterminedEnv) x
  -- return (RD PE.undeterminedEnv) <$ x 

refineValue :: forall b. Typeable b => Maybe (EqI b) -> Maybe (EqI b)
refineValue x =
  case eqT :: Maybe (b :~: ()) of
    Just Refl -> Just (EqI ())
    _         -> x


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
                        in tryUpdateEnv v (liftA2 pair (refineValue a) (refineValue b)) e

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
            a      = fmap EqI $ refineValue b >>= \b' -> case b' of
                                                           EqI bb -> finv bb
        in tryUpdateEnv v a e 



  ftext s = fromP $ G.text s
  
  fcat f g = PExp $ \tenv -> 
    let p = unPExp f tenv
        q = unPExp g tenv 
    in (\x y -> join (liftA2 k x y)) <$> p <*> q 
    where
      k :: Result env D -> Result env D -> Err (Result env D)
      k (RD env) (RD env') = RD <$> merge env env'

      merge :: Env env -> Env env -> Err (Env env)
      merge e e' = 
        case PE.mergeEnv mergeEqI e e' of
          Nothing  -> err $ D.text "Merge failed: update is consistent."
          Just env -> -- trace (show $ D.text "merging" D.<+> pprEnv e D.<+> pprEnv e' D.<+> D.nest 2 (D.text "->" D.</> pprEnv env)) $
                      return env 


  
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
    return $ PExp $ \tenv' -> -- trace (show tenv ++ "->" ++ show tenv') $
                              fmap (mapToEnv $ PE.embedEnv tenv tenv') <$> g 


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

data BlockCommentSpec =
  BlockCommentSpec { bcOpen  :: String    -- ^ The opening string for block comments
                   , bcClose :: String    -- ^ The closing string for block comments 
                   , bcNestable :: Bool   -- ^ Nestable or not 
                   }
data CommentSpec =
  CommentSpec { lcSpec :: Maybe String,             -- ^ Starting string for line comments 
                bcSpec :: Maybe BlockCommentSpec }  -- ^ Spec for block comments.


fromCommentSpec :: CommentSpec -> G.Grammar Char ()
fromCommentSpec (CommentSpec lc bc) = G.finalize $ do
  let glc = case lc of
              Nothing -> A.empty
              Just s  -> () <$ G.text s <* many (G.termSet nb) <* G.termSet br 
  rec gbc <-
        case bc of
          Nothing       -> return A.empty
          Just (BlockCommentSpec op cl isNestable) -> 
            if isNestable then do
              nonOpCl <- non [op, cl]
              G.share $ () <$ G.text op <* nonOpCl <* many (gbc <* nonOpCl) <* G.text cl
            else do
              nonCl   <- non [cl]
              return $ () <$  G.text op <* nonCl <* G.text cl 
  
  let gsp = () <$ G.termSet sp 
  return $ glc <|> gbc <|> gsp 
  where
    sp = RS.fromList " \r\n\t\v\f"
    br = RS.fromList "\n\r" 
    nb = RS.complement br 
    

non :: [String] -> RefM s (G.OpenGrammar s Char ())
non ss = G.share $ () <$ many (go ss)
  where
    -- invaliant: ss is a list of nonempty strings 
    go ss =
      let firsts = RS.fromList (map head ss)
          ss'    = map tail ss 
      in G.termSet (RS.complement firsts) <|>
         if any null ss' then
           A.empty
         else
           foldr (<|>) A.empty [ G.term f *> go [ tail s | s <- ss, head s == f ] | f <- RS.toList firsts ] 




parsingMode :: In a => FliPpr (a :~> D) -> G.Grammar Char (Err a)
parsingMode = parsingModeSP gsp
  where
    gsp = G.finalize $ return $ () <$ (foldr1 (<|>) $ map G.text [" ", "\n", "\r", "\t"])

parsingModeWith :: In a => CommentSpec -> FliPpr (a :~> D) -> G.Grammar Char (Err a)
parsingModeWith = parsingModeSP . fromCommentSpec

parsingModeSP :: In a => G.Grammar Char () -> FliPpr (a :~> D) -> G.Grammar Char (Err a)
parsingModeSP gsp (FliPpr m) =
  let g   = parsingModeMono m
  in G.thawSpace gsp $ G.inline $ G.removeNonProductive $ G.optSpaces g 
