{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE RebindableSyntax          #-}
{-# LANGUAGE RecursiveDo               #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE TypeOperators             #-}

-- |
-- This module implements parser-generation interpretation of FliPpr.
module Text.FliPpr.Internal.ParserGeneration (
  parsingMode, parsingModeMono, parsingModeSP, parsingModeWith,
  BlockCommentSpec(..), CommentSpec (..),
  PArg(..), PExp(..), Result(..),
 )  where

import           Control.Applicative             (Applicative (..), (<|>))
import qualified Control.Applicative             as A (empty)
import           Control.Monad                   (join, void)
import           Data.Foldable                   (asum)
import           Prelude                         hiding (Applicative (..))
-- import qualified Text.FliPpr.Internal.GrammarST as G

import           Data.Functor.Compose            (Compose (..))
import           Data.Functor.Identity           (Identity (..))
import qualified Data.RangeSet.List              as RS
import           Data.Typeable                   (Proxy (..))

import           Debug.Trace
import qualified Text.FliPpr.Doc                 as D
import           Text.FliPpr.Err                 (Err (..), err)
import qualified Text.FliPpr.Grammar             as G
import qualified Text.FliPpr.Internal.Defs       as Defs
import qualified Text.FliPpr.Internal.PartialEnv as PE
import           Text.FliPpr.Internal.Type

import           Data.Bifunctor                  (bimap)

import           Data.Kind                       (Type)

ifThenElse :: Bool -> p -> p -> p
ifThenElse True x _  = x
ifThenElse False _ y = y

-- import Debug.Trace

type PEImpl = PE.UB

type Rep = PE.Rep PEImpl

type Env = PE.Env PEImpl EqI

type Var = PE.Var PEImpl

data EqI a where
  EqI :: Eq a => a -> EqI a

mergeEqI :: EqI a -> EqI a -> Maybe (EqI a)
mergeEqI (EqI a) (EqI b)
  | a == b = Just (EqI a)
  | otherwise = Nothing

newtype PArg a = PArg {unPArg :: forall r. Rep r -> Var r a}

newtype PExp e t = PExp {unPExp :: forall r. G.Grammar G.ExChar e => Rep r -> e (Err (Result r t))}

type GU e a = G.Grammar G.ExChar e => e a

data Result env t where
  RD :: Env env -> Result env D
  RF :: Result (a ': env) t -> Result env (a ~> t)

{-# ANN applySem "HLint: ignore Avoid lambda using `infix`" #-}

applySem ::
  GU s (Err (Result r (a ~> t))) ->
  Var r a ->
  GU s (Err (Result r t))
applySem g v = (>>= \res -> appSem res v) <$> g

appSem :: Result r (a ~> t) -> Var r a -> Err (Result r t)
appSem (RF res) v =
  mapToEnvA
    ( \env ->
        let (a, e) = PE.popEnv env
         in tryUpdateEnv v a e
    )
    res

mapToEnvA ::
  Applicative f =>
  (Env env -> f (Env env')) ->
  Result env t ->
  f (Result env' t)
mapToEnvA f (RD e) = RD <$> f e
mapToEnvA f (RF e0) =
  RF
    <$> mapToEnvA
      ( \env ->
          let (a, e) = PE.popEnv env
           in extEnv a <$> f e
      )
      e0
  where
    extEnv a e = case PE.extendEnv e a of
      (e', _, _) -> e'

mapToEnv :: (Env env -> Env env') -> Result env t -> Result env' t
mapToEnv f = runIdentity . mapToEnvA (Identity . f)

tryUpdateEnv :: Var env a -> Maybe (EqI a) -> Env env -> Err (Env env)
tryUpdateEnv _ Nothing env = return env
tryUpdateEnv k (Just v0) env =
  case PE.updateEnv mergeEqI k v0 env of
    Just env' ->
      -- trace (show $ pprEnv env D.<+> D.text "->" D.<+> D.align (pprEnv env')) $
      return env'
    Nothing ->
      err
        ( D.text "The same variable is updated twice:"
            D.$$ D.text "updating position" D.<+> pprVar k D.<+> D.text "in" D.<+> PE.pprEnv env
        )
  where
    pprVar v = D.ppr (PE.toIndex v)

choice :: PExp s D -> PExp s D -> PExp s D
choice p q = PExp $ \tenv -> unPExp p tenv <|> unPExp q tenv

choiceGen :: PExp s r -> PExp s r -> PExp s r
choiceGen p q = PExp $ \tenv -> unPExp p tenv <|> unPExp q tenv

fromP :: GU s a -> PExp s D
fromP x = PExp $ \tenv -> return (RD (PE.undeterminedEnv tenv)) <$ x

-- return (RD PE.undeterminedEnv) <$ x

-- refineValue :: forall b. Typeable b => Maybe (EqI b) -> Maybe (EqI b)
-- refineValue x =
--   case eqT :: Maybe (b :~: ()) of
--     Just Refl -> Just (EqI ())
--     _         -> x

instance FliPprE PArg (PExp s) where
  fapp :: forall a t. PExp s (a ~> t) -> PArg a -> PExp s t
  fapp (PExp f) (PArg n) =
    PExp $ \tenv -> applySem (f tenv) (n tenv)

  farg :: forall a t. (PArg a -> PExp s t) -> PExp s (a ~> t)
  farg f = PExp $ \tenv ->
    case PE.extendRep tenv Proxy of
      (tenva, va, _vt) ->
        let a = PArg $ \tenv' -> PE.embedVar tenva tenv' va
         in fmap RF <$> unPExp (f a) tenva

  funpair ::
    forall a b r.
    (In a, In b) =>
    PArg (a, b) ->
    (PArg a -> PArg b -> PExp s r) ->
    PExp s r
  funpair inp f = PExp $ \tenv ->
    let (tenva, va, _) = PE.extendRep tenv Proxy
        (tenvb, vb, _) = PE.extendRep tenva Proxy
        argA = PArg $ \tenv' -> PE.embedVar tenva tenv' va
        argB = PArg $ \tenv' -> PE.embedVar tenvb tenv' vb
     in (>>= updateP (unPArg inp tenv)) <$> unPExp (f argA argB) tenvb
    where
      updateP :: Var env (a, b) -> Result (b : a : env) r -> Err (Result env r)
      updateP v = mapToEnvA $
        \eab ->
          let (b, ea) = PE.popEnv eab
              (a, e) = PE.popEnv ea
           in tryUpdateEnv v (liftA2 pair a b) e

      pair :: EqI a -> EqI b -> EqI (a, b)
      pair (EqI a) (EqI b) = EqI (a, b)

  fununit (PArg a) e = PExp $ \tenv ->
    let pos = a tenv
     in (>>= mapToEnvA (tryUpdateEnv pos (Just (EqI ())))) <$> unPExp e tenv

  fcase _ [] = PExp $ const A.empty
  fcase ex0 (Branch p pk : bs) = branch ex0 p pk `choiceGen` fcase ex0 bs
    where
      branch :: (In a) => PArg a -> PartialBij a b -> (PArg b -> PExp s r) -> PExp s r
      branch inp (PartialBij _ _ finv) k =
        PExp $ \tenv ->
          let (tenvb, vb, _) = PE.extendRep tenv Proxy
              argB = PArg $ \tenv' -> PE.embedVar tenvb tenv' vb
           in (>>= updateB finv (unPArg inp tenv)) <$> unPExp (k argB) tenvb

      updateB ::
        (In a) =>
        (b -> Maybe a) ->
        Var env a ->
        Result (b : env) r ->
        Err (Result env r)
      updateB finv v = mapToEnvA $ \eb ->
        let (b, e) = PE.popEnv eb
            a = fmap EqI $ b >>= \(EqI bb) -> finv bb
        in tryUpdateEnv v a e

  fcharAs a cs = PExp $ \tenv ->
    let x = unPArg a tenv
    in (\ c -> do { env <- tryUpdateEnv x (Just $ EqI $ unNormalChar c) (PE.undeterminedEnv tenv); return $ RD env })
       <$> G.symbI (RS.fromRangeList $ map (bimap G.NormalChar G.NormalChar) $ RS.toRangeList cs)
    where
      unNormalChar (G.NormalChar c) = c
      unNormalChar _                = error "Cannot happen."

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
          Nothing -> err $ D.text "Merge failed: update is consistent."
          Just env ->
            -- trace (show $ D.text "merging" D.<+> pprEnv e D.<+> pprEnv e' D.<+> D.nest 2 (D.text "->" D.</> pprEnv env)) $
            return env

  fbchoice = choice

  fempty = fromP $ G.text ""

  fspace = fromP G.space
  fspaces = fromP G.spaces

  fnespaces' = fromP G.spaces

  fline = fromP $ G.space <* G.spaces
  fline' = fspaces
  flinebreak = fspaces

  falign = id
  fgroup = id
  fnest _ = id

-- type family ResT (r :: [Type]) (a :: DType FType) = t | t -> a where
--   ResT r (T t) = T (Err (Result r t))
--   ResT r (a :*: b) = ResT r a :*: ResT r b

type family Map (f :: FType -> Type) as where
  Map f '[] = '[]
  Map f (a ': as) = f a ': Map f as
instance (G.Grammar G.ExChar g, Defs.Defs g) => Defs.Defs (PExp g) where
  -- newtype Fs (PExp g) a = RulesG {unRulesG :: forall r. Rep r -> Defs.Fs g (Defs.TransD (Compose Err (Result r)) a)}
  newtype D (PExp g) as a = RulesG { unRulesG :: forall r. Rep r -> Defs.D g (Map (Compose Err (Result r)) as) (Err (Result r a)) }

  liftD x = RulesG $ \tenv -> Defs.liftD (unPExp x tenv)
  unliftD (RulesG x) = PExp $ \tenv -> Defs.unliftD (x tenv)

  consD x y = RulesG $ \tenv ->
    Defs.consD (Compose <$> unPExp x tenv) (unRulesG y tenv)

  -- unpairRules (x :: Rules (PExp g) (a :*: b)) k = RulesG $ \(tenv :: Rep r) ->
  --   case propTransDPreservesDefType @a @(Compose Err (Result r)) of
  --     Wit -> case propTransDPreservesDefType @b @(Compose Err (Result r)) of
  --       Wit -> unpairRules (unRulesG x tenv) $ \a b ->
  --         let a' = RulesG $ \tenv' -> rmap (fmap $ h tenv tenv') a
  --             b' = RulesG $ \tenv' -> rmap (fmap $ h tenv tenv') b
  --          in unRulesG (k a' b') tenv
  --   where
  --     h :: Rep r -> Rep r' -> Compose Err (Result r) t -> Compose Err (Result r') t
  --     h tenv tenv' = Compose . fmap (mapToEnv (PE.embedEnv tenv tenv')) . getCompose

  letrD h = RulesG $ \tenv ->
    Defs.letrD $ \a ->
      let harg = PExp $ \tenv' -> fmap (mapToEnv (PE.embedEnv tenv tenv')) . getCompose <$> a
      in unRulesG (h harg) tenv

-- newtype PM s a = PM {runPM :: forall env. ReaderT (Rep env) (RefM s) a}

-- instance Functor (PM s) where
--   fmap f (PM m) = PM (fmap f m)

-- instance Applicative (PM s) where
--   pure a = PM (pure a)
--   PM f <*> PM a = PM (f <*> a)

-- instance Monad (PM s) where
--   return = pure
--   PM m >>= f = PM $ m >>= runPM . f

-- instance MonadFix (PM s) where
--   mfix f = PM (mfix (runPM . f))

-- data SomeRep = forall env. SomeRep (Rep env)

-- askRep :: PM s SomeRep
-- askRep = PM $ SomeRep <$> ask

-- instance FliPprD (PM s) PArg (PExp s) where
--   fshare (PExp e) = do
--     SomeRep tenv <- askRep
--     g <- PM $ lift $ G.share (e tenv)
--     return $
--       PExp $ \tenv' -> -- trace (show tenv ++ "->" ++ show tenv') $
--         fmap (mapToEnv $ PE.embedEnv tenv tenv') <$> g

--   flocal m = PExp $ \tenv ->
--     G.OpenG $ do
--       e <- runReaderT (runPM m) tenv
--       r <- G.runOpenG $ unPExp e tenv
--       return r

-- -- instance FliPprE PArg PExp where
-- --   ffix :: Container2 k =>
-- --           k (Rec k PExp) -> C PExp (k PExp)
-- --   ffix defs =
-- --     CPS $ \k -> PExp $ \(tenv :: Rep env) ->
-- --      let toPExp :: forall a. (GU :.: (Err :.: Result env)) a -> PExp a
-- --          toPExp   = makeArg tenv
-- --          fromPExp :: forall a. PExp a -> (GU :.: (Err :.: Result env)) a
-- --          fromPExp = run tenv
-- --      in unlift $
-- --          runCPS (G.gfixGen (fmap2 (adjustRec2 fromPExp toPExp) defs))
-- --                 (fromPExp . k . fmap2 toPExp)

-- --     -- unlift $ runCPS
-- --     --  (G.gfixGen
-- --     --    (fmap2 (\r -> Rec $ \x -> run tenv $ runRec r (fmap2 (makeArg tenv) x)) defs))
-- --     --  (\xs -> run tenv $ k (fmap2 (makeArg tenv) xs))
-- --     where
-- --       run :: Rep env -> PExp a -> (GU :.: (Err :.: Result env)) a
-- --       run tenv p = lift (unPExp p tenv)

-- --       makeArg :: Rep env -> (GU :.: (Err :.: Result env)) a -> PExp a
-- --       makeArg tenv g' =
-- --         let g = unlift g'
-- --         in PExp $ \tenv' -> fmap (mapToEnv (PE.embedEnv tenv tenv')) <$> g

-- --       lift :: forall f g h (a :: k). Functor f => f (g (h a)) -> (f :.: (g :.: h)) a
-- --       lift x = Comp (fmap Comp x)

-- --       unlift :: forall f g h (a :: k). Functor f => (f :.: (g :.: h)) a -> f (g (h a))
-- --       unlift x = fmap getComp (getComp x)

-- --   flet :: PExp a -> C PExp (PExp a)
-- --   flet a = cps $ \k -> PExp $ \tenv ->
-- --     runCPS (G.gshare (unPExp a tenv))
-- --            (\p -> unPExp (k (PExp $ \tenv' ->
-- --                             fmap (mapToEnv $ PE.embedEnv tenv tenv') <$> p))
-- --                   tenv)

parsingModeMono :: G.GrammarD G.ExChar g => PExp (G.Simplify G.ExChar g) (a ~> D) -> g (Err a)
parsingModeMono e =
  G.simplifyGrammar $ k <$> unPExp e PE.emptyRep
  where
    k :: Err (Result '[] (a ~> D)) -> Err a
    k (Fail s) = err $ D.text "Inverse computation fails: " D.</> s
    k (Ok a) = case a of
      RF (RD env) ->
        let (v, _) = PE.popEnv env
        in case v of
             Just (EqI u) -> return u
             Nothing      -> err $ D.text "Input is unused in evaluation."

-- parsingModeMono :: In a => (forall s. PM s (PExp s (a ~> D))) -> G.Grammar G.ExChar (Err a)
-- parsingModeMono m = G.finalize $ do
--   e <- runReaderT (runPM m) PE.emptyRep
--   return $ k <$> unPExp e PE.emptyRep
--   where
--     k :: In a => Err (Result '[] (a ~> D)) -> Err a
--     k (Fail s) = err $ D.text "Inverse computation fails: " D.</> s
--     k (Ok a) =
--       case a of
--         RF (RD e) ->
--           -- xtrace (show $ PE.pprEnv e) $
--           let (a, _) = PE.popEnv e
--            in case a of
--                 Just (EqI a) -> return a
--                 Nothing -> err $ D.text "Input is unused in evaluation."

data BlockCommentSpec = BlockCommentSpec
  { -- | The opening string for block comments
    bcOpen     :: String,
    -- | The closing string for block comments
    bcClose    :: String,
    -- | Nestable or not
    bcNestable :: Bool
  }

data CommentSpec = -- | Spec for block comments.
  CommentSpec
  { -- | Starting string for line comments
    lcSpec :: Maybe String,
    -- | Spec for block comments.
    bcSpec :: Maybe BlockCommentSpec
  }

-- | Make a grammar that represents a single space
fromCommentSpec :: G.GrammarD Char g => CommentSpec -> g ()
fromCommentSpec (CommentSpec lc bc) = G.local $ do
  lineComment <- G.share $ case lc of
    Nothing -> A.empty
    Just s  -> void (G.text s) <* many (G.symbI nb) <* G.symbI br

  rec blockComment <- case bc of
        Nothing -> G.rule A.empty
        Just (BlockCommentSpec op cl isNestable) ->
          if isNestable
            then do
              nonOpCl <- non [op, cl]
              G.rule $ void (G.text op) <* nonOpCl <* many (G.nt blockComment <* nonOpCl) <* G.text cl
            else do
              nonCl <- non [cl]
              G.rule $ void (G.text op) <* nonCl <* G.text cl

  singleSpace <- G.share $ void (G.symbI sp)
  return (lineComment <|> G.nt blockComment <|> singleSpace)
  where
    mfix = G.mfixDefM

    many :: G.GrammarD c g => g a -> g [a]
    many = G.manyD

    non :: G.GrammarD Char g => [String] -> Defs.DefM g (g ()) -- (Defs.Rules g (Defs.Lift ()))
    non strings = G.share $ void (many (go strings))
      where
        go :: G.Grammar Char g => [String] -> g Char
        go ss =
          G.symbI (RS.complement firsts)
            <|> if any null rests
              then A.empty
              else asum [G.symb f *> go [tail s | s <- ss, head s == f] | f <- RS.toList firsts]
          where
            firsts = RS.fromList $ map head ss
            rests = map tail ss

    sp = RS.fromList " \r\n\t\v\f" -- spaces
    br = RS.fromList "\r\n" -- breaks
    nb = RS.complement br -- non-breaks

-- fromCommentSpec :: CommentSpec -> G.Grammar Char ()
-- fromCommentSpec (CommentSpec lc bc) = G.finalize $ do
--   let glc = case lc of
--         Nothing -> A.empty
--         Just s -> () <$ G.text s <* many (G.termSet nb) <* G.termSet br
--   rec gbc <-
--         case bc of
--           Nothing -> return A.empty
--           Just (BlockCommentSpec op cl isNestable) ->
--             if isNestable
--               then do
--                 nonOpCl <- non [op, cl]
--                 G.share $ () <$ G.text op <* nonOpCl <* many (gbc <* nonOpCl) <* G.text cl
--               else do
--                 nonCl <- non [cl]
--                 return $ () <$ G.text op <* nonCl <* G.text cl

--   let gsp = () <$ G.termSet sp
--   return $ glc <|> gbc <|> gsp
--   where
--     sp = RS.fromList " \r\n\t\v\f"
--     br = RS.fromList "\n\r"
--     nb = RS.complement br

-- non :: [String] -> RefM s (G.OpenGrammar s Char ())
-- non ss = G.share $ () <$ many (go ss)
--   where
--     -- invaliant: ss is a list of nonempty strings
--     go ss =
--       let firsts = RS.fromList (map head ss)
--           ss' = map tail ss
--        in G.termSet (RS.complement firsts)
--             <|> if any null ss'
--               then A.empty
--               else foldr (<|>) A.empty [G.term f *> go [tail s | s <- ss, head s == f] | f <- RS.toList firsts]

-- parsingMode :: In a => FliPpr (a ~> D) -> G.Grammar Char (Err a)
-- parsingMode = parsingModeSP gsp
--   where
--     gsp = G.finalize $ return $ () <$ (foldr1 (<|>) $ map G.text [" ", "\n", "\r", "\t"])

parsingMode :: (G.GrammarD Char g) => FliPpr (a ~> D) -> g (Err a)
parsingMode = parsingModeWith spec
  where
    spec = CommentSpec {lcSpec = Nothing, bcSpec = Nothing}

-- parsingModeWith :: In a => CommentSpec -> FliPpr (a ~> D) -> G.Grammar Char (Err a)
-- parsingModeWith = parsingModeSP . fromCommentSpec

parsingModeWith :: forall g a. (G.GrammarD Char g) => CommentSpec -> FliPpr (a ~> D) -> g (Err a)
parsingModeWith spec (FliPpr e) =
  let g0 :: forall g'. (G.GrammarD G.ExChar g') => g' (Err a)
      g0 = parsingModeMono e
      g1 :: forall g'. (G.GrammarD Char g') => g' (Err a)
      g1 = G.withSpace (fromCommentSpec spec) (parsingModeMono e)
  in trace (show $ G.pprAsFlat g0 D.</> D.text "---------" D.</> G.pprAsFlat g1) g1

parsingModeSP :: forall g a. (G.GrammarD Char g) => (forall g'. G.GrammarD Char g' => g' ()) -> FliPpr (a ~> D) -> g (Err a)
parsingModeSP gsp (FliPpr e) =
  G.withSpace gsp (parsingModeMono e)

-- parsingModeSP :: In a => G.Grammar Char () -> FliPpr (a ~> D) -> G.Grammar Char (Err a)
-- parsingModeSP gsp (FliPpr m) =
--   let g = parsingModeMono m
--    in G.thawSpace gsp $ G.inline $ G.removeNonProductive $ G.optSpaces g
