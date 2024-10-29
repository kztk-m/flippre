{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Text.FliPpr.Grammar.Flatten (flatten, freeze) where

import Control.Applicative (Alternative (..), Const (..))
import Data.Kind (Type)
import Data.Proxy (Proxy (..))

import Data.RangeSet.List (RSet)

import Defs
import Unembedding as U
import Unembedding.Env (Env (..), Ix (..))

import Control.Category
import Prelude hiding (id, (.))
import qualified Prelude (id, (.))

import Data.Function.Compat (applyWhen)
import Prettyprinter hiding (SEmpty)
import Text.FliPpr.Grammar.Types
import qualified Unembedding.Env as U

data FreeGrammarExp c env a where
  FNT :: Ix env a -> FreeGrammarExp c env a
  FSymb :: c -> FreeGrammarExp c env c
  FSymbI :: RSet c -> FreeGrammarExp c env c
  FStar :: FreeGrammarExp c env (a -> b) -> FreeGrammarExp c env a -> FreeGrammarExp c env b
  FPure :: a -> FreeGrammarExp c env a
  FAlt :: FreeGrammarExp c env a -> FreeGrammarExp c env a -> FreeGrammarExp c env a
  FEmp :: FreeGrammarExp c env a
  UnliftT :: FreeGrammarD c env '[] r -> FreeGrammarExp c env r

prettyE :: (Show c) => Int -> Env (Const Int) env -> FreeGrammarExp c env a -> Doc ann
prettyE _ xs (FNT x) = "x_" <> unsafeViaShow (getConst $ U.lookEnv xs x)
prettyE k _ (FSymb c) =
  applyWhen (k > 9) parens $
    "symb" <+> unsafeViaShow c
prettyE k _ (FSymbI cs) =
  applyWhen (k > 9) parens $ "symbI" <+> unsafeViaShow cs
prettyE k xs (FStar e1 e2) =
  applyWhen (k > 4) parens $
    prettyE 4 xs e1 <+> "<*>" <+> prettyE 5 xs e2
prettyE k _ (FPure _) =
  applyWhen (k > 9) parens "pure _"
prettyE k xs (FAlt e1 e2) =
  align $
    group $
      applyWhen (k > 3) parens $
        vsep [prettyE 3 xs e1, "<|>" <+> prettyE 4 xs e2]
prettyE _ _ FEmp = "empty"
prettyE k xs (UnliftT d) =
  align $ group $ applyWhen (k > 9) parens $ "liftD" <+> prettyD 10 xs d

instance (Show c, env ~ '[]) => Pretty (FreeGrammarExp c env a) where
  pretty = prettyE 0 ENil

prettyD :: (Show c) => Int -> Env (Const Int) env -> FreeGrammarD c env as r -> Doc ann
prettyD k xs (ConsT e d) =
  applyWhen (k > 9) parens $ "consD" <+> prettyE 10 xs e <+> prettyD 10 xs d
prettyD k xs (LiftT e) =
  applyWhen (k > 9) parens $ "liftD" <+> prettyE 10 xs e
prettyD k xs (LetrT d) =
  applyWhen (k > 9) parens $ "letrD" <+> body
  where
    body =
      parens . align . group $
        ("\\ x_" <> pretty n <+> "->")
          <+> align (group $ prettyD 0 (ECons (Const n) xs) d)
    n = U.lenEnv xs

data FreeGrammarD c env as r where
  ConsT :: FreeGrammarExp c env a -> FreeGrammarD c env as r -> FreeGrammarD c env (a : as) r
  LiftT :: FreeGrammarExp c env r -> FreeGrammarD c env '[] r
  LetrT :: FreeGrammarD c (a : env) (a : as) r -> FreeGrammarD c env as r

instance (Show c, env ~ '[]) => Pretty (FreeGrammarD c env as r) where
  pretty = prettyD 0 ENil

data UType = ExpT Type | DeclT [Type] Type

-- | Witness that @as@ must has the form of @[ExpT a1,..., ExpT an]@, where @as' = [a1,...,an]@.
data ComesFromExpT (as :: [UType]) (as' :: [Type]) where
  NilOk :: ComesFromExpT '[] '[]
  ConsOk :: ComesFromExpT as as' -> ComesFromExpT (ExpT a : as) (a : as')

data UExp c (env :: [Type]) (u :: UType) where
  FromE :: FreeGrammarExp c env a -> UExp c env (ExpT a)
  FromD :: FreeGrammarD c env as r -> UExp c env (DeclT as r)

unFromE :: UExp c env (ExpT a) -> FreeGrammarExp c env a
unFromE (FromE e) = e

unFromD :: UExp c env (DeclT as r) -> FreeGrammarD c env as r
unFromD (FromD d) = d

newtype USem c uenv u
  = USem {unUSem :: forall env. ComesFromExpT uenv env -> UExp c env u}

instance LiftVariables (USem c) where
  newtype Var (USem c) env a = VarUSem (Ix env a)
    deriving newtype Variables

  liftVar (VarUSem x0) = USem $ \wit -> conv wit x0 (FromE . FNT)
    where
      conv ::
        ComesFromExpT uenv env
        -> Ix uenv a
        -> (forall b. (a ~ ExpT b) => Ix env b -> r)
        -> r
      conv w (IxS x) = case w of
        ConsOk w' -> \k -> conv w' x $ \x' -> k (IxS x')
      conv w IxZ = case w of
        ConsOk _ -> \k -> k IxZ

-- These functions are costly.
-- TODO: Avoid them as possible by providing FromSymb, Applicative, Alternative instances fo
-- EnvI (USem c) instead of EnvI (FreeGrammarExp c).
liftExp :: EnvI (FreeGrammarExp c) a -> EnvI (USem c) (ExpT a)
liftExp (EnvI f) = EnvI $ \tenv -> USem $ \wit -> FromE $ f (convTEnv tenv wit)
  where
    convTEnv :: TEnv as -> ComesFromExpT as as' -> TEnv as'
    convTEnv ENil NilOk = ENil
    convTEnv (ECons _ ps) (ConsOk w) = ECons Proxy (convTEnv ps w)

unliftExp :: EnvI (USem c) (ExpT a) -> EnvI (FreeGrammarExp c) a
unliftExp (EnvI f) = EnvI $ \tenv -> genTEnv tenv $ \wit tenv' ->
  unFromE (unUSem (f tenv') wit)
  where
    genTEnv :: TEnv as -> (forall as'. ComesFromExpT as' as -> TEnv as' -> r) -> r
    genTEnv ENil = \k -> k NilOk ENil
    genTEnv w0 = \k -> case w0 of
      ECons _ w ->
        genTEnv w $ \wit tenv -> k (ConsOk wit) (ECons Proxy tenv)

-- newtype EnvIT c u = EnvIT (forall a. (u ~ ExpT a) => EnvI (USem c) u)

-- toEnvIT :: EnvI (USem c) (ExpT a) -> EnvIT c (ExpT a)
-- toEnvIT = EnvIT

-- instance Defs (EnvIT c) where
--   newtype D (EnvIT c) us u
--     = DEnvI
--     { runDEnvI ::
--         forall as r.
--         (ExpT r ~ u) =>
--         ComesFromExpT us as
--         -> EnvI (USem c) (DeclT as r)
--     }

--   consD (EnvIT e) (DEnvI d) = DEnvI $ \(ConsOk dwit) -> U.liftFO2 consT' e (d dwit)
--     where
--       consT' :: USem c env (ExpT a) -> USem c env (DeclT as r) -> USem c env (DeclT (a : as) r)
--       consT' (USem fe) (USem fd) = USem $ \wit ->
--         FromD (ConsT (unFromE $ fe wit) (unFromD $ fd wit))

--   liftD (EnvIT e) = DEnvI $ \(NilOk) -> U.liftFO1 liftT' e
--     where
--       liftT' :: USem c env (ExpT a) -> USem c env (DeclT '[] a)
--       liftT' (USem fe) = USem $ \wit -> FromD $ LiftT (unFromE $ fe wit)

--   unliftD (DEnvI d) = EnvIT $ U.liftFO1 unliftT' (d NilOk)
--     where
--       unliftT' :: USem c env (DeclT '[] r) -> USem c env (ExpT r)
--       unliftT' (USem fd) = USem $ \wit ->
--         let FromD d1 = fd wit
--         in  FromE $ UnliftT d1

--   letrD :: forall a as r. (EnvIT c a -> D (EnvIT c) (a : as) r) -> D (EnvIT c) as r
--   letrD h = DEnvI $ \dwit ->
--     U.liftSOn (ol1 :. End) letrT' (h' dwit)
--     where
--       h' :: (r ~ ExpT r1) => ComesFromExpT as as1 -> EnvI (USem c) (ExpT a0) -> EnvI (USem c) (DeclT (a0 : as1) r1)
--       h' dwit x = runDEnvI (h (toEnvIT x)) (ConsOk dwit)

--       letrT' :: USem c (ExpT a' : env) (DeclT (a' : as') r') -> USem c env (DeclT as' r')
--       letrT' (USem fd) = USem $ \wit ->
--         let FromD d1 = fd (ConsOk wit)
--         in  FromD $ LetrT d1

instance Defs (EnvI (FreeGrammarExp c)) where
  newtype D (EnvI (FreeGrammarExp c)) as r = DD {runDD :: EnvI (USem c) (DeclT as r)}

  consD e (DD d) = DD $ U.liftFO2 consT' (liftExp e) d
    where
      consT' :: USem c env (ExpT a) -> USem c env (DeclT as r) -> USem c env (DeclT (a : as) r)
      consT' (USem fe) (USem fd) = USem $ \wit ->
        FromD (ConsT (unFromE $ fe wit) (unFromD $ fd wit))

  liftD e = DD $ U.liftFO1 liftT' (liftExp e)
    where
      liftT' :: USem c env (ExpT a) -> USem c env (DeclT '[] a)
      liftT' (USem fe) = USem $ \wit ->
        FromD $ LiftT (unFromE $ fe wit)

  unliftD (DD d) = unliftExp $ U.liftFO1 unliftT' d
    where
      unliftT' :: USem c env (DeclT '[] r) -> USem c env (ExpT r)
      unliftT' (USem fd) = USem $ \wit ->
        let FromD d1 = fd wit
        in  FromE $ UnliftT d1

  letrD h = DD $ U.liftSOn (ol1 :. End) letrT' $ \x ->
    runDD (h (unliftExp x))
    where
      letrT' :: USem c (ExpT a : env) (DeclT (a : as) r) -> USem c env (DeclT as r)
      letrT' (USem fd) = USem $ \wit ->
        let FromD d1 = fd (ConsOk wit)
        in  FromD $ LetrT d1

instance FromSymb c (EnvI (FreeGrammarExp c)) where
  symb c = U.liftFO0 (FSymb c)
  symbI cs = U.liftFO0 (FSymbI cs)

instance Functor (EnvI (FreeGrammarExp c)) where
  fmap f x = pure f <*> x -- intentional

instance Applicative (EnvI (FreeGrammarExp c)) where
  pure x = U.liftFO0 (FPure x)
  (<*>) = U.liftFO2 FStar

instance Alternative (EnvI (FreeGrammarExp c)) where
  empty = U.liftFO0 FEmp
  (<|>) = U.liftFO2 FAlt
  many = manyD
  some = someD

freeze ::
  (forall e. (GrammarD c e) => e a)
  -> FreeGrammarExp c '[] a
freeze h =
  let USem x = U.runClose (liftExp h)
      FromE r = x NilOk
  in  r

-- >>> pretty $ freeze $ symb 'a'
-- symb 'a'
-- >>> pretty $ freeze $ unliftD $ letrD (\x -> consD (symb 'a') $ liftD x)
-- liftD (letrD (\ x_0 -> consD (symb 'a') (liftD x_0)))
-- >>> pretty $ freeze $ local $ do { x <- share (symb 'a'); pure x }
-- liftD (letrD (\ x_0 -> consD (symb 'a') (liftD x_0)))
-- >>> pretty $ freeze $ local $ do { Tip x <- mfixDefM $ \(Tip x) -> pure $ Tip $ symb 'a' *> x <|> pure 1; pure x }
-- liftD (letrD (\ x_0 -> consD (pure _ <*> symb 'a' <*> x_0
--                              <|> pure _) (liftD x_0)))

newtype DiffF env1 env2
  = DiffF {shift :: forall a. Ix env1 a -> Ix env2 a}

diffStep :: DiffF env (a : env)
diffStep = DiffF weaken

diffTail :: DiffF env env' -> DiffF (a : env) (a : env')
diffTail (DiffF diff) = DiffF $ \case
  IxZ -> IxZ
  (IxS x) -> IxS (diff x)

instance Category DiffF where
  id = DiffF Prelude.id
  DiffF f . DiffF g = DiffF (f Prelude.. g)

data SpecRHS = Empty | Singleton | Other
data SSpecRHS (c :: SpecRHS) where
  SEmpty :: SSpecRHS 'Empty
  SSingleton :: SSpecRHS 'Singleton
  SOther :: SSpecRHS 'Other

data SizedRHS c env (b :: SpecRHS) a where
  EmptyRHS :: SizedRHS c env 'Empty a
  SingRHS :: !(Prod c env a) -> SizedRHS c env 'Singleton a
  OtherRHS :: ![Prod c env a] -> SizedRHS c env 'Other a

unsize :: SizedRHS c env s a -> RHS c env a
unsize EmptyRHS = MkRHS []
unsize (SingRHS p) = MkRHS [p]
unsize (OtherRHS ps) = MkRHS ps

-- | A type representing an A-normalization result.
data ANormalizeRes c env1 a
  = forall env2 s.
    ANormalizeRes
      (DiffF env1 env2)
      -- ^ witnessing the resulting env2 is at least as large as the original
      (SSpecRHS s)
      -- ^ Size of RHS it produces. This information is used to determine @env2@
      ( forall envf.
        DiffF env2 envf
        -> ( Env (RHS c envf) env1 -> Env (RHS c envf) env2
           , SizedRHS c envf s a
           )
      )
      -- ^ @envf@: final environment
      --   @DiffF env2 envf@: witnessing the final environment is at least as large as @env2@
      --   @Env (RHS c envf) env1 -> Env (RHS c envf) env2@: Definitions introduced, represented as a diff-list (@x1 = e1 ... xn = en@ of the resulting A-normal form @let x = e1 ... xn = en in e@)
      --   @SizedRHS c envf s a@: Resulting term (@e@ of @let x = e1 ... xn = en in e@)

data ANormalizeResD c env1 as r
  = forall env2 sr.
    ANormalizeResD
      (DiffF env1 env2)
      (SSpecRHS sr)
      ( forall envf.
        DiffF env2 envf -- withness that envf is at least as large as env2
        -> ( Env (RHS c envf) env1 -> Env (RHS c envf) env2
           , Env (RHS c envf) as
           , SizedRHS c envf sr r -- the resulting environment and term
           )
      )

aNormalize ::
  FreeGrammarExp c env a
  -> DiffF env env1
  -> ANormalizeRes c env1 a
aNormalize (FSymb c) _diff0 = ANormalizeRes id SSingleton $ const (id, SingRHS (fromSymb (Symb c)))
aNormalize (FSymbI cs) _ = ANormalizeRes id SSingleton $ const (id, SingRHS (fromSymb (SymbI cs)))
aNormalize (FNT x) diff0 = ANormalizeRes id SSingleton $ \diffF ->
  (id, SingRHS (fromSymb (NT $ shift (diffF . diff0) x)))
aNormalize (FPure a) _diff0 = ANormalizeRes id SSingleton $ const (id, SingRHS (pure a))
aNormalize (FStar e1 e2) diff0
  | ANormalizeRes diff1 sdecl1 h1 <- aNormalize e1 diff0
  , ANormalizeRes diff2 sdecl2 h2 <- aNormalize e2 (diff1 . diff0) =
      case (sdecl1, sdecl2) of
        (SEmpty, _) -> ANormalizeRes id SEmpty $ const (id, EmptyRHS)
        (_, SEmpty) -> ANormalizeRes id SEmpty $ const (id, EmptyRHS)
        (SSingleton, SSingleton) -> ANormalizeRes (diff2 . diff1) SSingleton $ \diffF ->
          let (decls1, SingRHS p1) = h1 (diffF . diff2)
              (decls2, SingRHS p2) = h2 diffF
          in  (decls2 . decls1, SingRHS (p1 <*> p2))
        (_, _) -> ANormalizeRes (diffStep . diffStep . diff2 . diff1) SSingleton $ \diffF ->
          let (decls1, r1) = h1 (diffF . diffStep . diffStep . diff2)
              (decls2, r2) = h2 (diffF . diffStep . diffStep)
              d = ECons (unsize r1) . ECons (unsize r2) . decls2 . decls1
              x1 = shift diffF IxZ
              x2 = shift diffF (IxS IxZ)
          in  (d, SingRHS $ fromSymb (NT x1) <*> fromSymb (NT x2))
aNormalize FEmp _diff0 = ANormalizeRes id SEmpty $ const (id, EmptyRHS)
aNormalize (FAlt e1 e2) diff0
  | ANormalizeRes diff1 sdecl1 h1 <- aNormalize e1 diff0
  , ANormalizeRes diff2 sdecl2 h2 <- aNormalize e2 (diff1 . diff0) =
      case (sdecl1, sdecl2) of
        (SEmpty, _) -> ANormalizeRes (diff2 . diff1) sdecl2 $ \diffF ->
          let (decls1, _) = h1 (diffF . diff2)
              (decls2, r) = h2 diffF
          in  (decls2 . decls1, r)
        (_, SEmpty) -> ANormalizeRes (diff2 . diff1) sdecl1 $ \diffF ->
          let (decls1, r) = h1 (diffF . diff2)
              (decls2, _) = h2 diffF
          in  (decls2 . decls1, r)
        (_, _) -> ANormalizeRes (diff2 . diff1) SOther $ \diffF ->
          let (decls1, r1) = h1 (diffF . diff2)
              (decls2, r2) = h2 diffF
          in  (decls2 . decls1, OtherRHS $ getProds (unsize r1) ++ getProds (unsize r2))
aNormalize (UnliftT d) diff0
  | ANormalizeResD diff1 sd h1 <- aNormalizeD d diff0 = ANormalizeRes diff1 sd $ \diffF ->
      let (decls1, _, r) = h1 diffF
      in  (decls1, r)

aNormalizeD ::
  FreeGrammarD c env as a
  -> DiffF env env1
  -> ANormalizeResD c env1 as a
aNormalizeD (ConsT e d) diff0
  | ANormalizeRes diff1 _sdecls1 h1 <- aNormalize e diff0
  , ANormalizeResD diff2 sdecls2 h2 <- aNormalizeD d (diff1 . diff0) =
      ANormalizeResD (diff2 . diff1) sdecls2 $ \diffF ->
        let (decls1, r1) = h1 (diffF . diff2)
            (decls2, rs, r2) = h2 diffF
        in  (decls2 . decls1, ECons (unsize r1) rs, r2)
aNormalizeD (LiftT e) diff0
  | ANormalizeRes diff1 sdecls1 h1 <- aNormalize e diff0 =
      ANormalizeResD diff1 sdecls1 $ \diffF ->
        let (decls1, r1) = h1 diffF
        in  (decls1, ENil, r1)
aNormalizeD (LetrT d) diff0
  | ANormalizeResD diff1 sdecls1 h1 <- aNormalizeD d (diffTail diff0) =
      ANormalizeResD (diff1 . diffStep) sdecls1 $ \diffF ->
        let (declsD, ECons a as, r) = h1 diffF
        in  (declsD . ECons a, as, r)

flatten :: (forall e. (GrammarD c e) => e a) -> FlatGrammar c a
flatten e =
  case aNormalize (freeze e) id of
    ANormalizeRes _ _ h ->
      let (decls, r) = h id
      in  FlatGrammar (decls ENil) (unsize r)

-- >>> pretty $ flatten $ symb 'a'
-- 'a'
-- >>> pretty $ flatten $ unliftD $ letrD (\x -> consD (symb 'a') $ liftD x)
-- N0
--   where
--     N0 ::= 'a'
-- >>> pretty $ flatten $ local $ do { x <- share (symb 'a'); pure x }
-- N0
--   where
--     N0 ::= 'a'
-- >>> pretty $ flatten $ local $ do { Tip x <- mfixDefM $ \(Tip x) -> pure $ Tip $ symb 'a' *> x <|> pure (1 :: Int); pure x }
-- N0
--   where
--     N0 ::= 'a' N0 | <EMPTY>
