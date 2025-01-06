{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- |
-- This module implements parser-generation interpretation of FliPpr.
module Text.FliPpr.Internal.ParserGeneration (
  parsingMode,
  parsingModeMono,
  parsingModeSP,
  parsingModeWith,
  BlockCommentSpec (..),
  CommentSpec (..),
  -- PArg (..),
  -- PExp (..),
  Result (..),
) where

import Control.Applicative (Alternative, Applicative (..), (<|>))
import qualified Control.Applicative as A (empty)
import Control.Monad (join, void)
import Data.Foldable (asum)
import Data.Functor.Compose (Compose (..))
import Data.Functor.Identity (Identity (..))
import Data.Kind (Type)
import Data.String (IsString (..))
import Data.Typeable (Proxy (..))
import Prelude hiding (Applicative (..))

import Data.Bifunctor (bimap)
import Data.Functor ((<&>))
import qualified Data.RangeSet.List as RS
import qualified Prettyprinter as PP

-- import Debug.Trace
import qualified Defs
import qualified Text.FliPpr.Grammar as G
import Text.FliPpr.Grammar.Err (Err (..), err)
import Text.FliPpr.Internal.Type

import GHC.Stack (HasCallStack, callStack, prettyCallStack)
import qualified Unembedding as U
import Unembedding.Env (Env (..))

class ValEnvRepr r where
  type Index r :: [Type] -> Type -> Type
  data ValEnv r :: [Type] -> Type

  popEnv :: ValEnv r (a : env) -> (Maybe a, ValEnv r env)
  mapTailA :: (Applicative f) => (ValEnv r env -> f (ValEnv r env')) -> ValEnv r (a : env) -> f (ValEnv r (a : env'))
  mapHeadA :: (Applicative f) => (Maybe a -> f (Maybe b)) -> ValEnv r (a : env) -> f (ValEnv r (b : env))
  undeterminedEnv :: ValEnv r env

  weakenEnv :: ValEnv r env -> ValEnv r (a : env)

  updateEnv :: (HasCallStack) => Index r env a -> a -> ValEnv r env -> Err ann (ValEnv r env)
  mergeEnv :: ValEnv r env -> ValEnv r env -> Err ann (ValEnv r env)

data UsingIx

unVCons :: ValEnv UsingIx (a : as) -> (Maybe a, ValEnv UsingIx as)
unVCons VEmpty = (Nothing, VEmpty)
unVCons (VCons a as) = (a, as)

instance ValEnvRepr UsingIx where
  type Index UsingIx = G.Ix
  data ValEnv UsingIx as where
    VEmpty :: ValEnv UsingIx as
    VCons :: !(Maybe a) -> ValEnv UsingIx as -> ValEnv UsingIx (a : as)

  popEnv = unVCons

  {-# SPECIALIZE mapTailA :: (ValEnv UsingIx env -> Identity (ValEnv UsingIx env')) -> ValEnv UsingIx (a : env) -> Identity (ValEnv UsingIx (a : env')) #-}
  mapTailA f (unVCons -> (a, as)) = VCons a <$> f as

  mapHeadA f (unVCons -> (a, as)) = (`VCons` as) <$> f a

  undeterminedEnv = VEmpty

  weakenEnv VEmpty = VEmpty
  weakenEnv as = VCons Nothing as

  updateEnv G.IxZ a (unVCons -> (p, as)) =
    case p of
      Nothing -> pure $ VCons (Just a) as
      Just _ -> err "Multiple use of a variable"
  updateEnv (G.IxS x) v (unVCons -> (a, as)) = VCons a <$> updateEnv x v as

  mergeEnv VEmpty venv = pure venv
  mergeEnv venv VEmpty = pure venv
  mergeEnv (VCons p1 venv1) (VCons p2 venv2) = VCons <$> mergeVal p1 p2 <*> mergeEnv venv1 venv2
    where
      mergeVal Nothing m = pure m
      mergeVal m Nothing = pure m
      mergeVal (Just _) (Just _) = err "Multiple use of a variable"

newtype ArgSem r env a = ArgSem (Index r env a)

deriving newtype instance (U.Weakenable (Index r)) => U.Weakenable (ArgSem r)
deriving newtype instance (U.Variables (Index r)) => U.Variables (ArgSem r)

instance (U.Variables (Index r)) => U.LiftVariables (ArgSem r)

newtype ExpSem r ann g env t = ExpSem {expSem :: g (Err ann (Result r env t))}

-- Parsing result
data Result r env t where
  RF :: !(Result r (a : env) t) -> Result r env (a ~> t)
  RD :: !(ValEnv r env) -> Result r env D

type PExp ann g t = U.EnvI (ExpSem UsingIx ann g) t

-- appSem :: e1
--   e1 results in ValEnv r (env' ++ a : env)
--   a points to a in env
--
appSem :: (ValEnvRepr r, Functor g) => ExpSem r ann g env (a ~> t) -> ArgSem r env a -> ExpSem r ann g env t
appSem (ExpSem e) (ArgSem ix_) = ExpSem $ (fmap . (=<<)) (\(RF res) -> f ix_ res) e
  where
    f :: (ValEnvRepr r) => Index r env a -> Result r (a : env) t -> Err ann (Result r env t)
    f ix = mapToEnvA $ \env ->
      let (vv, env') = popEnv env
      in  maybe (pure env') (\v -> updateEnv ix v env') vv

mapToEnvA ::
  (Applicative f, ValEnvRepr r) =>
  (ValEnv r env -> f (ValEnv r env'))
  -> Result r env t
  -> f (Result r env' t)
mapToEnvA f (RD e) = RD <$> f e
mapToEnvA f (RF e0) = RF <$> mapToEnvA (mapTailA f) e0
{-# SPECIALIZE mapToEnvA :: (ValEnvRepr r) => (ValEnv r env -> Identity (ValEnv r env')) -> Result r env t -> Identity (Result r env' t) #-}

mapToEnv ::
  (ValEnvRepr r) =>
  (ValEnv r env -> ValEnv r env')
  -> Result r env t
  -> Result r env' t
mapToEnv f = runIdentity . mapToEnvA (Identity . f)

noresult :: (Applicative f, ValEnvRepr r, Functor g) => g b -> g (f (Result r env D))
noresult g = pure (RD undeterminedEnv) <$ g

newtype WithExtendedEnv a r ann g env t = WithExtendedEnv (g (Err ann (Result r (a : env) t)))

brHOAS :: (ValEnvRepr r, Functor g, U.Variables (Index r), HasCallStack) => Branch (U.EnvI (ArgSem r)) (U.EnvI (ExpSem r ann g)) a t -> U.EnvI (WithExtendedEnv a r ann g) t
brHOAS (Branch (PartialBij pname _ finv) pk) = brHOASImpl pname finv pk

brHOASImpl ::
  forall r ann g a b t.
  (ValEnvRepr r, Functor g, U.Variables (Index r), HasCallStack) =>
  String
  -> (b -> Maybe a)
  -> (U.EnvI (ArgSem r) b -> U.EnvI (ExpSem r ann g) t)
  -> U.EnvI (WithExtendedEnv a r ann g) t
brHOASImpl pname finv = U.liftSOn' @(ArgSem r) @(WithExtendedEnv a r ann g) (U.ol1 :. ENil) Proxy h
  where
    replaceHead :: ValEnv r (b : env) -> Err ann (ValEnv r (a : env))
    replaceHead =
      mapHeadA $ \case
        Nothing -> err $ PP.vcat [PP.hsep ["Detected unused variable in the branch:", fromString pname], fromString $ prettyCallStack callStack]
        Just b -> do
          maybe (err $ PP.hsep ["Inverse pattern matching failed:", fromString pname]) (pure . Just) $ finv b

    h :: ExpSem r ann g (b : env) t -> WithExtendedEnv a r ann g env t
    h (ExpSem g) = WithExtendedEnv $ (fmap . (=<<)) (mapToEnvA replaceHead) g

branchesHOAS :: (ValEnvRepr r, Alternative g, U.Variables (Index r), HasCallStack) => [Branch (U.EnvI (ArgSem r)) (U.EnvI (ExpSem r ann g)) a t] -> U.EnvI (WithExtendedEnv a r ann g) t
branchesHOAS =
  foldr
    ( U.liftFO2
        ( \(WithExtendedEnv e1) (WithExtendedEnv e2) ->
            WithExtendedEnv (e1 <|> e2)
        )
        . brHOAS
    )
    (U.liftFO0 (WithExtendedEnv A.empty))

instance (ValEnvRepr r, U.Variables (Index r), G.Grammar G.ExChar g) => FliPprE (U.EnvI (ArgSem r)) (U.EnvI (ExpSem r ann g)) where
  fapp = U.liftFO2' appSem

  farg = U.liftSOn' @(ArgSem r) @(ExpSem r ann g) (U.ol1 :. ENil) Proxy lamSem
    where
      lamSem :: ExpSem r ann g (a : env) t -> ExpSem r ann g env (a :~> t)
      lamSem (ExpSem e) = ExpSem $ fmap (fmap RF) e

  fcase a bs = U.liftFO2' scrutineeSem a (branchesHOAS bs)
    where
      scrutineeSem :: forall env a t. ArgSem r env a -> WithExtendedEnv a r ann g env t -> ExpSem r ann g env t
      scrutineeSem (ArgSem ix) (WithExtendedEnv g) = ExpSem $ (fmap . (=<<)) (mapToEnvA f) g
        where
          f :: ValEnv r (a : env) -> Err ann (ValEnv r env)
          f venv = case popEnv venv of
            (Nothing, _) -> err "Cannot happen."
            (Just v, venv') -> updateEnv ix v venv'
  funpair = U.liftSOn' @(ArgSem r) @(ExpSem r ann g) (U.ol0 :. U.ol2 :. ENil) Proxy unpairSem
    where
      unpairSem ::
        ArgSem r env (a, b)
        -> ExpSem r ann g (a : b : env) t
        -> ExpSem r ann g env t
      unpairSem (ArgSem ix) (ExpSem e) = ExpSem $ e <&> \m -> m >>= mapToEnvA (upd ix)

      upd :: Index r env (a1, b1) -> ValEnv r (a1 : b1 : env) -> Err ann (ValEnv r env)
      upd ix venv = do
        let (a, rest1) = popEnv venv
            (b, rest2) = popEnv rest1
        case (a, b) of
          (Just va, Just vb) -> updateEnv ix (va, vb) rest2
          (Nothing, Nothing) -> pure rest2 -- defer error
          (Just _, Nothing) -> err $ PP.vcat [fromString "funpair: the second element of a pair is not used", fromString $ prettyCallStack callStack]
          (Nothing, Just _) -> err $ PP.vcat [fromString "funpair: the first element of a pair is not used", fromString $ prettyCallStack callStack]

  fununit = U.liftFO2' ununitSem
    where
      ununitSem :: ArgSem r env () -> ExpSem r ann g env t -> ExpSem r ann g env t
      ununitSem (ArgSem ix) (ExpSem e) = ExpSem $ fmap (>>= mapToEnvA (updateEnv ix ())) e

  fbchoice = U.liftFO2 bchoiceSem
    where
      bchoiceSem (ExpSem e1) (ExpSem e2) = ExpSem $ e1 <|> e2
  fcharAs e cs = U.liftFO1' charAsSem e
    where
      charAsSem :: ArgSem r env Char -> ExpSem r ann g env D
      charAsSem (ArgSem ix) =
        ExpSem $
          symbI' cs' <&> \c ->
            RD <$> updateEnv ix (unNormalChar c) undeterminedEnv

      cs' = RS.fromRangeList $ map (bimap G.NormalChar G.NormalChar) $ RS.toRangeList cs

      symbI' :: (G.FromSymb G.ExChar s) => RS.RSet G.ExChar -> s G.ExChar
      symbI' cs_
        | RS.size cs_ == 1 = G.symb $ RS.findMin cs_
        | otherwise = G.symbI cs_

      unNormalChar :: G.ExChar -> Char
      unNormalChar (G.NormalChar c) = c
      unNormalChar _ = error "Cannot happen."

  ftext str = U.liftFO0 $ ExpSem $ noresult $ G.text str
  fabort = U.liftFO0 $ ExpSem A.empty
  fempty = U.liftFO0 $ ExpSem $ noresult $ G.text ""
  fcat = U.liftFO2 $ \(ExpSem e1) (ExpSem e2) -> ExpSem $ (\x y -> join (liftA2 merge x y)) <$> e1 <*> e2
    where
      merge :: Result r env D -> Result r env D -> Err ann (Result r env D)
      merge (RD venv1) (RD venv2) = RD <$> mergeEnv venv1 venv2

  fspace = U.liftFO0 $ ExpSem $ noresult G.space
  fspaces = U.liftFO0 $ ExpSem $ noresult G.spaces
  fline = U.liftFO0 $ ExpSem $ noresult $ G.space <* G.spaces
  flinebreak = fspaces
  fline' = fspaces
  fnespaces' = fspaces
  falign = id
  fgroup = id
  fnest = const id

type family Fst (p :: (k1, k2)) :: k1 where
  Fst '(a, b) = a

type family Snd (p :: (k1, k2)) :: k2 where
  Snd '(a, b) = b

type family Map (f :: FType -> Type) as where
  Map f '[] = '[]
  Map f (a ': as) = f a ': Map f as

type ErrResult ann r env = Compose (Err ann) (Result r env)

newtype WrapD r ann g env asres = WrapD {unwrapD :: Defs.D g (Map (ErrResult ann r env) (Fst asres)) (Err ann (Result r env (Snd asres)))}

-- instance U.LiftVariables (ExpSem rep ann g)

instance (Functor g, ValEnvRepr rep) => U.Weakenable (ExpSem rep ann g) where
  weaken (ExpSem g) = ExpSem $ (fmap . fmap) (mapToEnv weakenEnv) g

-- TODO: Define weakenMany as well for performance

instance (Defs g, U.Variables (Index rep), ValEnvRepr rep, Applicative g) => Defs (U.EnvI (ExpSem rep ann g)) where
  newtype D (U.EnvI (ExpSem rep ann g)) as r = DE {runDE :: U.EnvI (WrapD rep ann g) '(as, r)}
  liftD = DE . U.liftFO1' liftSem
    where
      liftSem :: ExpSem rep ann g env a -> WrapD rep ann g env '( '[], a)
      liftSem (ExpSem ge) = WrapD $ G.liftD ge
  unliftD (DE d) = U.liftFO1' unliftSem d
    where
      unliftSem :: WrapD rep ann g env '( '[], a) -> ExpSem rep ann g env a
      unliftSem (WrapD gd) = ExpSem $ G.unliftD gd
  consD e (DE d) = DE $ U.liftFO2' consSem e d
    where
      consSem :: ExpSem rep ann g env a -> WrapD rep ann g env '(as, r) -> WrapD rep ann g env '(a : as, r)
      consSem (ExpSem ge) (WrapD gd) = WrapD $ G.consD (Compose <$> ge) gd
  letrD h = DE $ U.liftSOnGen @(ArgSem rep) @(WrapD rep ann g) (U.DimNested (U.K U.E) :. ENil) Proxy letrDSem (runDE . h)
    where
      letrDSem ::
        (ExpSem rep ann g env a -> WrapD rep ann g env '(a : as, r))
        -> WrapD rep ann g env '(as, r)
      letrDSem hh = WrapD $ Defs.letrD $ \a -> unwrapD $ hh (ExpSem $ fmap getCompose a)

-- DE $ U.liftFO0' $ WrapD $ Defs.letrD $ \a -> U.runEnvI (runDE (h _)) _

-- DE $ U.EnvI $ \tenv -> WrapD $ Defs.letrD $ \a ->
-- let x = U.EnvI $ \tenv' -> ExpSem $ fmap (mapToEnv (embedEnv tenv tenv')) . getCompose <$> a
-- in  unwrapD $ U.runEnvI (runDE $ h x) tenv

-- ifThenElse :: Bool -> p -> p -> p
-- ifThenElse True x _ = x
-- ifThenElse False _ y = y

-- -- import Debug.Trace

-- type PEImpl = PE.UB

-- type Rep = PE.Rep PEImpl

-- type Env = PE.Env PEImpl EqI

-- type Var = PE.Var PEImpl

-- data EqI a where
--   EqI :: (Eq a) => a -> EqI a

-- mergeEqI :: EqI a -> EqI a -> Maybe (EqI a)
-- mergeEqI (EqI a) (EqI b)
--   | a == b = Just (EqI a)
--   | otherwise = Nothing

-- newtype PArg a = PArg {unPArg :: forall r. Rep r -> Var r a}

-- newtype PExp ann e t = PExp {unPExp :: forall r. (G.Grammar G.ExChar e) => Rep r -> e (Err ann (Result r t))}

-- type GU e a = (G.Grammar G.ExChar e) => e a

-- data Result env t where
--   RD :: Env env -> Result env D
--   RF :: Result (a ': env) t -> Result env (a ~> t)

-- {-# ANN applySem ("HLint: ignore Avoid lambda using `infix`" :: String) #-}
-- applySem ::
--   GU s (Err ann (Result r (a ~> t)))
--   -> Var r a
--   -> GU s (Err ann (Result r t))
-- applySem g v = (>>= \res -> appSem res v) <$> g

-- appSem :: Result r (a ~> t) -> Var r a -> Err ann (Result r t)
-- appSem (RF res) v =
--   mapToEnvA
--     ( \env ->
--         let (a, e) = PE.popEnv env
--         in  tryUpdateEnv v a e
--     )
--     res

-- mapToEnvA ::
--   (Applicative f) =>
--   (Env env -> f (Env env'))
--   -> Result env t
--   -> f (Result env' t)
-- mapToEnvA f (RD e) = RD <$> f e
-- mapToEnvA f (RF e0) =
--   RF
--     <$> mapToEnvA
--       ( \env ->
--           let (a, e) = PE.popEnv env
--           in  extEnv a <$> f e
--       )
--       e0
--   where
--     extEnv a e = case PE.extendEnv e a of
--       (e', _, _) -> e'

-- mapToEnv :: (Env env -> Env env') -> Result env t -> Result env' t
-- mapToEnv f = runIdentity . mapToEnvA (Identity . f)

-- tryUpdateEnv :: Var env a -> Maybe (EqI a) -> Env env -> Err ann (Env env)
-- tryUpdateEnv _ Nothing env = return env
-- tryUpdateEnv k (Just v0) env =
--   case PE.updateEnv mergeEqI k v0 env of
--     Just env' ->
--       -- trace (show $ pprEnv env D.<+> D.text "->" D.<+> D.align (pprEnv env')) $
--       return env'
--     Nothing ->
--       err
--         ( PP.vcat
--             [ "The same variable is updated twice:"
--             , "updating position" PP.<+> pprVar k PP.<+> "in" PP.<+> PE.pprEnv env
--             ]
--         )
--   where
--     pprVar v = PP.pretty (PE.toIndex v)

-- choice :: PExp ann s D -> PExp ann s D -> PExp ann s D
-- choice p q = PExp $ \tenv -> unPExp p tenv <|> unPExp q tenv

-- choiceGen :: PExp ann s r -> PExp ann s r -> PExp ann s r
-- choiceGen p q = PExp $ \tenv -> unPExp p tenv <|> unPExp q tenv

-- fromP :: GU s a -> PExp ann s D
-- fromP x = PExp $ \tenv -> return (RD (PE.undeterminedEnv tenv)) <$ x

-- -- return (RD PE.undeterminedEnv) <$ x

-- -- refineValue :: forall b. Typeable b => Maybe (EqI b) -> Maybe (EqI b)
-- -- refineValue x =
-- --   case eqT :: Maybe (b :~: ()) of
-- --     Just Refl -> Just (EqI ())
-- --     _         -> x

-- instance FliPprE PArg (PExp ann s) where
--   fapp :: forall a t. PExp ann s (a ~> t) -> PArg a -> PExp ann s t
--   fapp (PExp f) (PArg n) =
--     PExp $ \tenv -> applySem (f tenv) (n tenv)

--   farg :: forall a t. (PArg a -> PExp ann s t) -> PExp ann s (a ~> t)
--   farg f = PExp $ \tenv ->
--     case PE.extendRep tenv Proxy of
--       (tenva, va, _vt) ->
--         let a = PArg $ \tenv' -> PE.embedVar tenva tenv' va
--         in  fmap RF <$> unPExp (f a) tenva

--   funpair ::
--     forall a b r ann.
--     (In a, In b) =>
--     PArg (a, b)
--     -> (PArg a -> PArg b -> PExp ann s r)
--     -> PExp ann s r
--   funpair inp f = PExp $ \tenv ->
--     let (tenva, va, _) = PE.extendRep tenv Proxy
--         (tenvb, vb, _) = PE.extendRep tenva Proxy
--         argA = PArg $ \tenv' -> PE.embedVar tenva tenv' va
--         argB = PArg $ \tenv' -> PE.embedVar tenvb tenv' vb
--     in  (>>= updateP (unPArg inp tenv)) <$> unPExp (f argA argB) tenvb
--     where
--       updateP :: Var env (a, b) -> Result (b : a : env) r -> Err ann (Result env r)
--       updateP v = mapToEnvA $
--         \eab ->
--           let (b, ea) = PE.popEnv eab
--               (a, e) = PE.popEnv ea
--           in  tryUpdateEnv v (liftA2 pair a b) e

--       pair :: EqI a -> EqI b -> EqI (a, b)
--       pair (EqI a) (EqI b) = EqI (a, b)

--   fununit (PArg a) e = PExp $ \tenv ->
--     let pos = a tenv
--     in  (>>= mapToEnvA (tryUpdateEnv pos (Just (EqI ())))) <$> unPExp e tenv

--   fabort = PExp $ const A.empty

--   fcase _ [] = PExp $ const A.empty
--   fcase ex0 (Branch p pk : bs) = branch ex0 p pk `choiceGen` fcase ex0 bs
--     where
--       branch :: (In a) => PArg a -> PartialBij a b -> (PArg b -> PExp ann s r) -> PExp ann s r
--       branch inp (PartialBij _ _ finv) k =
--         PExp $ \tenv ->
--           let (tenvb, vb, _) = PE.extendRep tenv Proxy
--               argB = PArg $ \tenv' -> PE.embedVar tenvb tenv' vb
--           in  (>>= updateB finv (unPArg inp tenv)) <$> unPExp (k argB) tenvb

--       updateB ::
--         (In a) =>
--         (b -> Maybe a)
--         -> Var env a
--         -> Result (b : env) r
--         -> Err ann (Result env r)
--       updateB finv v = mapToEnvA $ \eb ->
--         let (b, e) = PE.popEnv eb
--             a = fmap EqI $ b >>= \(EqI bb) -> finv bb
--         in  tryUpdateEnv v a e

--   fcharAs a cs = PExp $ \tenv ->
--     let x = unPArg a tenv
--     in  (\c -> do env <- tryUpdateEnv x (Just $ EqI $ unNormalChar c) (PE.undeterminedEnv tenv); return $ RD env)
--           <$> symbI' (RS.fromRangeList $ map (bimap G.NormalChar G.NormalChar) $ RS.toRangeList cs)
--     where
--       symbI' :: (G.FromSymb G.ExChar s) => RS.RSet G.ExChar -> s G.ExChar
--       symbI' cs_
--         | RS.size cs_ == 1 = G.symb $ RS.findMin cs_
--         | otherwise = G.symbI cs_

--       unNormalChar :: G.ExChar -> Char
--       unNormalChar (G.NormalChar c) = c
--       unNormalChar _ = error "Cannot happen."

--   ftext s = fromP $ G.text s

--   fcat f g = PExp $ \tenv ->
--     let p = unPExp f tenv
--         q = unPExp g tenv
--     in  (\x y -> join (liftA2 k x y)) <$> p <*> q
--     where
--       k :: Result env D -> Result env D -> Err ann (Result env D)
--       k (RD env) (RD env') = RD <$> merge env env'

--       merge :: Env env -> Env env -> Err ann (Env env)
--       merge e e' =
--         case PE.mergeEnv mergeEqI e e' of
--           Nothing -> err "Merge failed: update is consistent."
--           Just env ->
--             -- trace (show $ D.text "merging" D.<+> pprEnv e D.<+> pprEnv e' D.<+> D.nest 2 (D.text "->" D.</> pprEnv env)) $
--             return env

--   fbchoice = choice

--   fempty = fromP $ G.text ""

--   fspace = fromP G.space
--   fspaces = fromP G.spaces

--   fnespaces' = fromP G.spaces

--   fline = fromP $ G.space <* G.spaces
--   fline' = fspaces
--   flinebreak = fspaces

--   falign = id
--   fgroup = id
--   fnest _ = id

-- -- type family ResT (r :: [Type]) (a :: DType FType) = t | t -> a where
-- --   ResT r (T t) = T (Err (Result r t))
-- --   ResT r (a :*: b) = ResT r a :*: ResT r b

-- type family Map (f :: FType -> Type) as where
--   Map f '[] = '[]
--   Map f (a ': as) = f a ': Map f as
-- instance (G.Grammar G.ExChar g, Defs.Defs g) => Defs.Defs (PExp ann g) where
--   -- newtype Fs (PExp g) a = RulesG {unRulesG :: forall r. Rep r -> Defs.Fs g (Defs.TransD (Compose Err (Result r)) a)}
--   newtype D (PExp ann g) as a = RulesG {unRulesG :: forall r. Rep r -> Defs.D g (Map (Compose (Err ann) (Result r)) as) (Err ann (Result r a))}

--   liftD x = RulesG $ \tenv -> Defs.liftD (unPExp x tenv)
--   unliftD (RulesG x) = PExp $ \tenv -> Defs.unliftD (x tenv)

--   consD x y = RulesG $ \tenv ->
--     Defs.consD (Compose <$> unPExp x tenv) (unRulesG y tenv)

--   -- unpairRules (x :: Rules (PExp g) (a :*: b)) k = RulesG $ \(tenv :: Rep r) ->
--   --   case propTransDPreservesDefType @a @(Compose Err (Result r)) of
--   --     Wit -> case propTransDPreservesDefType @b @(Compose Err (Result r)) of
--   --       Wit -> unpairRules (unRulesG x tenv) $ \a b ->
--   --         let a' = RulesG $ \tenv' -> rmap (fmap $ h tenv tenv') a
--   --             b' = RulesG $ \tenv' -> rmap (fmap $ h tenv tenv') b
--   --          in unRulesG (k a' b') tenv
--   --   where
--   --     h :: Rep r -> Rep r' -> Compose Err (Result r) t -> Compose Err (Result r') t
--   --     h tenv tenv' = Compose . fmap (mapToEnv (PE.embedEnv tenv tenv')) . getCompose

--   letrD h = RulesG $ \tenv ->
--     Defs.letrD $ \a ->
--       let harg = PExp $ \tenv' -> fmap (mapToEnv (PE.embedEnv tenv tenv')) . getCompose <$> a
--       in  unRulesG (h harg) tenv

parsingModeMono :: (G.GrammarD G.ExChar g) => (forall f. (G.GrammarD G.ExChar f) => PExp ann f (a ~> D)) -> g (Err ann a)
parsingModeMono e =
  G.simplify $ k <$> expSem (U.runClose e)
  where
    k :: Err ann (Result UsingIx '[] (a ~> D)) -> Err ann a
    k (Fail s) = err $ PP.vsep ["Inverse computation fails: ", s]
    k (Ok a) = case a of
      RF (RD env) ->
        let (v, _) = popEnv env
        in  case v of
              Just u -> return u
              Nothing -> err "Input is unused in evaluation."

data BlockCommentSpec = BlockCommentSpec
  { bcOpen :: String
  -- ^ The opening string for block comments
  , bcClose :: String
  -- ^ The closing string for block comments
  , bcNestable :: Bool
  -- ^ Nestable or not
  }

data CommentSpec
  = -- | Spec for block comments.
    CommentSpec
    { lcSpec :: Maybe String
    -- ^ Starting string for line comments
    , bcSpec :: Maybe BlockCommentSpec
    -- ^ Spec for block comments.
    }

-- | Make a grammar that represents a single space
fromCommentSpec :: (G.GrammarD Char g) => CommentSpec -> g ()
fromCommentSpec (CommentSpec lc bc) = G.local $ do
  lineComment <- G.share $ case lc of
    Nothing -> A.empty
    Just s -> void (G.text s) <* many (G.symbI nb) <* G.symbI br

  blockComment <- G.mfixDefM $ \blockComment -> case bc of
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
    many :: (G.GrammarD c g) => g a -> g [a]
    many = G.manyD

    non :: (G.GrammarD Char g) => [String] -> Defs.DefM g (g ()) -- (Defs.Rules g (Defs.Lift ()))
    non strings = G.share $ void (many (go strings))
      where
        go :: (G.Grammar Char g) => [String] -> g Char
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

parsingMode :: (G.GrammarD Char g) => FliPpr (a ~> D) -> g (Err ann a)
parsingMode = parsingModeWith spec
  where
    spec = CommentSpec{lcSpec = Nothing, bcSpec = Nothing}

parsingModeWith :: forall g a ann. (G.GrammarD Char g) => CommentSpec -> FliPpr (a ~> D) -> g (Err ann a)
parsingModeWith spec (FliPpr e) =
  let g0 :: forall g'. (G.GrammarD G.ExChar g') => g' (Err ann a)
      g0 = parsingModeMono e
      g1 :: forall g'. (G.GrammarD Char g') => g' (Err ann a)
      g1 = G.withSpace (fromCommentSpec spec) (parsingModeMono e)
  in  -- trace (show $ PP.fillSep [G.pprAsFlat g0, fromString "---------", G.pprAsFlat g1])
      g1

parsingModeSP :: forall g a ann. (G.GrammarD Char g) => (forall g'. (G.GrammarD Char g') => g' ()) -> FliPpr (a ~> D) -> g (Err ann a)
parsingModeSP gsp (FliPpr e) =
  G.withSpace gsp (parsingModeMono e)

-- parsingModeSP :: In a => G.Grammar Char () -> FliPpr (a ~> D) -> G.Grammar Char (Err a)
-- parsingModeSP gsp (FliPpr m) =
--   let g = parsingModeMono m
--    in G.thawSpace gsp $ G.inline $ G.removeNonProductive $ G.optSpaces g
