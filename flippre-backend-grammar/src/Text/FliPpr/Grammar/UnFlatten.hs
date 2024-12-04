{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Text.FliPpr.Grammar.UnFlatten (unFlatten) where

import Control.Applicative (asum)
import Control.Monad.State (StateT (..), evalStateT)
import Data.Typeable ((:~:) (..))
import Defs as D
import Text.FliPpr.Grammar.Types

import qualified Text.FliPpr.Grammar.Internal.Map2 as M2

-- Just for test
-- import Text.FliPpr.Grammar.Flatten

import Text.FliPpr.Grammar.Internal.Util

type MemoS g env = M2.Map2 (Ix env) g

lookupEnvRec :: Env (RHS c env) env -> Ix env a -> RHS c env a
lookupEnvRec = go (const False)
  where
    go :: (forall x. Ix env x -> Bool) -> Env (RHS c env) env -> Ix env a -> RHS c env a
    go memo defs x
      | memo x = MkRHS []
      | otherwise =
          case lookEnv defs x of
            MkRHS [PCons (NT y) (PNil f)] ->
              f <$> go (\z -> case eqIx z x of Just _ -> True; _ -> memo z) defs y
            rhs -> rhs

-- | unflattens grammar with inlining.
unFlatten :: forall c g r. (GrammarD c g) => FlatGrammar c r -> g r
unFlatten (FlatGrammar (defs :: Env (RHS c env) env) rhs0) =
  local $ evalStateT (procRHS rhs0) M2.empty
  where
    -- initMemoS :: MemoS g env
    -- initMemoS = MemoS $ const Nothing

    -- updateMemoS :: MemoS g env -> Ix env a -> g a -> MemoS g env
    -- updateMemoS (MemoS m) x v = MemoS $ \x' ->
    --   case eqIx x x' of
    --     Just Refl -> Just v
    --     Nothing -> m x'

    procRHS :: RHS c env a -> StateT (MemoS g env) (DefM g) (g a)
    procRHS (MkRHS rs) = asum <$> mapM procProd rs

    procProd :: Prod c env a -> StateT (MemoS g env) (DefM g) (g a)
    procProd (PNil a) = return (pure a)
    procProd (PCons s r) = do
      s' <- procSymb s
      r' <- procProd r
      return $ (\a k -> k a) <$> s' <*> r'

    -- (fmap $ \a k -> k a) <$> procSymb s <*> procProd r

    -- x = rhs is inlinable if rhs is small enouch and x does not appear in rhs
    inlinable :: Ix env a -> RHS c env a -> Bool
    inlinable _ (MkRHS []) = True
    inlinable x (MkRHS [p]) = smallEnough p && not (occur p)
      where
        smallEnough :: Prod c env b -> Bool
        smallEnough (PNil _) = True
        smallEnough (PCons _ (PNil _)) = True
        smallEnough _ = False

        occur :: Prod c env b -> Bool
        occur (PNil _) = False
        occur (PCons (NT y) _) | Just _ <- eqIx x y = True
        occur (PCons _ r) = occur r
    inlinable _ _ = False

    procSymb :: Symb c env a -> StateT (MemoS g env) (DefM g) (g a)
    procSymb (Symb c) = return (symb c)
    procSymb (SymbI cs) = return (symbI cs)
    procSymb (NT x) = StateT $ \memo ->
      case M2.lookup x memo of
        Just r -> return (r, memo)
        Nothing -> do
          let rhs = lookupEnvRec defs x
          if inlinable x rhs
            then do
              (r, m) <- runStateT (procRHS rhs) memo
              return (r, M2.insert x r m)
            else letr1 $ \a -> do
              (r, m) <- runStateT (procRHS rhs) (M2.insert x a memo)
              return (r, (a, m))

_example :: FlatGrammar Char ()
_example = FlatGrammar defs (MkRHS [fromSymb (NT IxZ)])
  where
    --    defs :: Env (RHS Char _) _
    defs =
      ECons (MkRHS [pure (), fromSymb (Symb 'a') *> fromSymb (NT IxZ)]) $ ENil

-- >>> Prettyprinter.pretty _example
-- N0
--   where
--     N0 ::= <EMPTY> | 'a' N0

-- >>> Prettyprinter.pretty (freeze $ unFlatten _example)
-- liftD (letrD (\ x_0 -> consD (pure _
--                              <|> (pure _ <*> symb 'a' <*> (pure _ <*> x_0 <*> pure _)
--                                  <|> empty)) (liftD (pure _ <*> x_0 <*> pure _
--                                                     <|> empty))))

-- >>> Prettyprinter.pretty (flatten $ unFlatten _example)
-- N0
--   where
--     N0 ::= <EMPTY> | 'a' N0

-- -- data RHSwithInlinability c env a
-- --   = RHSYes (RHS c env a)
-- --   | RHSNo (RHS c env a)

-- -- inlinable :: RHS c env a -> Const Bool a
-- -- inlinable rhs@(MkRHS []) = Const True
-- -- inlinable rhs@(MkRHS [p]) | smallEnough p = Const True
-- -- inlinable rhs = Const False

-- -- smallEnough :: Prod c env a -> Bool
-- -- smallEnough (PNil _) = True -- empty string
-- -- smallEnough (PCons _ (PNil _)) = True -- single character
-- -- smallEnough _ = False

-- -- inlineStep :: (GrammarD c g) => Env g as -> Env (Const Bool) as -> Env g as
-- -- inlineStep env flags = _

-- data Inline f a = Inline {inlineFlag :: !InlineFlag, inlineBody :: f a}

-- data InlineFlag = OkNull | OkSingle | OkEmpty | OkNT | No

-- instance (FromSymb c f) => FromSymb c (Inline f) where
--   symb = Inline OkSingle . symb
--   symbI = Inline OkSingle . symbI

-- instance (Functor f) => Functor (Inline f) where
--   fmap f (Inline flag x) = Inline flag (fmap f x)

-- instance (Applicative f, Alternative f) => Applicative (Inline f) where
--   pure = Inline OkEmpty . pure
--   Inline OkNull _ <*> _ = Inline OkNull empty
--   _ <*> Inline OkNull _ = Inline OkNull empty
--   Inline OkEmpty f <*> x = Inline OkSingle (f <*> inlineBody x)
--   f <*> Inline OkEmpty x = Inline OkSingle (inlineBody f <*> x)
--   f <*> x = Inline No (inlineBody f <*> inlineBody x)

-- instance (Alternative f) => Alternative (Inline f) where
--   empty = Inline OkNull empty
--   Inline OkNull _ <|> x = x
--   x <|> Inline OkNull _ = x
--   x <|> y = Inline No (inlineBody x <|> inlineBody y)

--   many x = Inline No (many $ inlineBody x)
--   some x = Inline No (some $ inlineBody x)

-- inline ::
--   (FromSymb c f, Alternative f) =>
--   (forall ff. (FromSymb c ff, Alternative ff) => Env ff as -> (Env ff as, ff a))
--   -> Env f as
--   -> (Env f as, f a)
-- inline h xs =
--   let xs' = mapEnv (Inline OkNT) xs
--       (rs', r) = h xs'
--   in  _

-- unFlattenNaive :: forall c g r. (GrammarD c g) => FlatGrammar c r -> g r
-- unFlattenNaive (FlatGrammar defs e) = D.local $ do
--   let sh = mapEnv (const Proxy) defs
--       h = inline $ \xs -> (mapEnv (goRHS xs) defs, goRHS xs e)
--   go sh (pure . h)
--   where
--     go :: Env Proxy as -> (Env g as -> DefM g (Env g as, res)) -> DefM g res
--     go ENil h = snd <$> h ENil
--     go (ECons _ sh) h = D.letr1 $ \x -> go sh $ \xs -> do
--       (vss, r) <- h (ECons x xs)
--       case vss of
--         ECons v vs -> pure (vs, (v, r))

--     goRHS :: (FromSymb c f, Alternative f) => Env f env -> RHS c env a -> f a
--     goRHS env (MkRHS ps) = asum (map (goProd env) ps)

--     goProd :: (FromSymb c f, Applicative f) => Env f env -> Prod c env a -> f a
--     goProd _ (PNil a) = pure a
--     goProd env (PCons s r) = (&) <$> goSymb env s <*> goProd env r

--     goSymb :: (FromSymb c f) => Env f env -> Symb c env a -> f a
--     goSymb _ (Symb c) = symb c
--     goSymb _ (SymbI cs) = symbI cs
--     goSymb env (NT x) = lookEnv env x
