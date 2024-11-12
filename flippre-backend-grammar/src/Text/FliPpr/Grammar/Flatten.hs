{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module transforms grammars into flattened form.
-- The transformation consists of two steps:
--
--   1. Unembedding ('freeze')
--   2. A-normalization ('flatten')
module Text.FliPpr.Grammar.Flatten (flatten, freeze) where

import Control.Applicative (Alternative (..), Const (..))
import Data.Proxy (Proxy (..))

import Data.RangeSet.List (RSet)

import Defs
import Unembedding (Dim' (..), EnvI, LiftVariables (..), Variables (..))
import qualified Unembedding as U

import Control.Category (Category (..))
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
  -- | Corresponding to the follwing typing rule.
  --
  -- @
  --   Γ |- d : Dec ε B
  --  ------------------
  --   Γ |- local d : B
  -- @
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
  -- | Construct corresponding to the following rule
  --
  -- @
  --   Γ |- e : A    Γ |- d : Dec Δ B
  --   -------------------------------
  --     Γ |- e |> d : Dec (A, Δ) B
  -- @
  ConsT :: FreeGrammarExp c env a -> FreeGrammarD c env as r -> FreeGrammarD c env (a : as) r
  -- | Construct corresponding to the following rule
  --
  -- @
  --      Γ |- e : A
  --   ----------------------
  --   Γ |- ret e : Dec ε A
  -- @
  LiftT :: FreeGrammarExp c env r -> FreeGrammarD c env '[] r
  -- | Construct corresponding to the folowing rule
  --
  -- @
  --  Γ, x : A |- d : Dec (A, Δ) B
  --  -----------------------------
  --    Γ |- letr x. d : Dec Δ B
  -- @
  LetrT :: FreeGrammarD c (a : env) (a : as) r -> FreeGrammarD c env as r

instance (Show c, env ~ '[]) => Pretty (FreeGrammarD c env as r) where
  pretty = prettyD 0 ENil

newtype WrapD c env asr = WrapD (FreeGrammarD c env (Fst asr) (Snd asr))

type family Fst (p :: (k1, k2)) :: k1 where
  Fst '(a, b) = a

type family Snd (p :: (k1, k2)) :: k2 where
  Snd '(a, b) = b

instance LiftVariables (FreeGrammarExp c) where
  newtype Var (FreeGrammarExp c) env a = VarFE (Ix env a)
    deriving newtype Variables

  liftVar (VarFE ix) = FNT ix

instance Defs (EnvI (FreeGrammarExp c)) where
  newtype D (EnvI (FreeGrammarExp c)) as r = DD {runDD :: EnvI (WrapD c) '(as, r)}

  consD e0 (DD d0) = DD $ U.liftFO2' (\e (WrapD d) -> WrapD $ ConsT e d) e0 d0

  liftD = DD . U.liftFO1' (WrapD . LiftT)

  unliftD = U.liftFO1' (\(WrapD d) -> UnliftT d) . runDD

  letrD h = DD $ U.liftSOn' (U.ol1 ::. U.End') Proxy (\(WrapD d) -> WrapD (LetrT d)) (runDD . h)

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
freeze = U.runClose

-- let USem x = U.runClose (liftExp h)
--     FromE r = x NilOk
-- in  r

-- >>> pretty $ freeze $ symb 'a'
-- symb 'a'
-- >>> pretty $ freeze $ unliftD $ letrD (\x -> consD (symb 'a') $ liftD x)
-- liftD (letrD (\ x_0 -> consD (symb 'a') (liftD x_0)))
-- >>> pretty $ freeze $ local $ do { x <- share (symb 'a'); pure x }
-- liftD (letrD (\ x_0 -> consD (symb 'a') (liftD x_0)))
-- >>> pretty $ freeze $ local $ do { Tip x <- mfixDefM $ \(Tip x) -> pure $ Tip $ symb 'a' *> x <|> pure 1; pure x }
-- liftD (letrD (\ x_0 -> consD (pure _ <*> symb 'a' <*> x_0
--                              <|> pure _) (liftD x_0)))

--------------------
-- A Normalization
--------------------

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

-- | A type representing an A-normalization result. The basic idea is to hold
-- definitions @ds@ and resulting expression @e@ in the A-normalized form @let
-- ds in e@. Here, @ds@ corresponds to production rules of a grammar and @e@ to
-- the right-hand of the start symbol.
--
-- Very roughly speaking, the translation should behave as:
--
-- @
--    e1 --aNormalize--> ds1 / e1'
--    e2 --aNormalize--> ds2 / e2'
-- --------------------------------------------------------
--    e1 <|> e2 --aNormalize--> ds1 ++ ds2 / e1' ++ e2'
-- @
--
-- However, this is not straight forward as @ds1@ and @ds2@ may refer to
-- different environments. Also, we want to avoid concatenation of declarations:
-- since they are represented by heterogeneous lists, and concatenating them
-- comes also with type-level appends.
--
-- To address the situation, we:
--
--    * Enforce that @ds1@ and @ds2@ are index by the final environment, which
--      is made available only after A-normalization is over. Hence, we
--      universally quantify the type of the final environment, and pass around
--      the witness that it is at least as large as other environments involved.
--
--    * Use difference lists. Thus, for example, @ds1@ has type @Env (RHS c
--      envf) env1 -> Env (RHS c envf) env2@, where @env1@ is universally
--      quantified while @env2@ is existentially quantified.
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
  -- ^ Expression to normalize
  -> DiffF env env1
  -- ^ specifies @env1@.
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
