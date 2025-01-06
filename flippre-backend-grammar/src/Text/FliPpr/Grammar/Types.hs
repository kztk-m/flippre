{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Text.FliPpr.Grammar.Types (
  -- * Type class for grammars
  FromSymb (..),
  Grammar,
  GrammarD,

  -- * Datatype for flat CFGs
  FlatGrammar (..),
  UE.Ix (..),
  IxN (..),
  fromIx,
  toIx,
  Symb (..),
  fromSymb,
  Prod (..),
  RHS (..),

  -- * Treatment of environments
  UE.Env (..),
  UE.mapEnv,
  UE.lookEnv,
) where

import Data.RangeSet.List (RSet)
import qualified Data.RangeSet.List as RS

import Control.Applicative (Alternative (..))
import Defs (Defs (..))

import qualified Unembedding.Env as UE

import Data.Coerce (coerce)
import qualified Data.List.Split as Sp
import Data.String (IsString (..))
import qualified Prettyprinter as PP
import Unsafe.Coerce (unsafeCoerce)

class FromSymb c e | e -> c where
  -- | A production of a given single char.
  symb :: c -> e c
  symb = symbI . RS.singleton

  -- | A production of a single character taken from a given set.
  symbI :: RSet c -> e c

-- | A grammar expression. This class does not specify any ways to define
-- "nonterminals", which indeed is the role of 'Defs'.
type Grammar c e = (Alternative e, FromSymb c e)

type GrammarD c e = (Defs e, Grammar c e)

--------------

newtype IxN (env :: [k]) (a :: k) = IxN Word deriving stock Show

fromIx :: UE.Ix env a -> IxN env a
fromIx x0 = IxN (go x0 0)
  where
    go :: UE.Ix env' a' -> Word -> Word
    go UE.IxZ r = r
    go (UE.IxS x) r = go x $! r + 1

toIx :: IxN env a -> UE.Ix env a
toIx (IxN n0) = go n0 UE.IxZ unsafeCoerce
  where
    go :: Word -> UE.Ix env a -> (forall env'. UE.Ix env' a -> r) -> r
    go 0 x k = k x
    go n x k = go (n - 1) (UE.IxS x) k

data Symb c env a where
  NT :: !(IxN env a) -> Symb c env a
  Symb :: !c -> Symb c env c
  SymbI :: !(RSet c) -> Symb c env c

instance (Show c) => PP.Pretty (Symb c env a) where
  pretty (NT x) = fromString ("N" ++ show (go x))
    where
      go :: IxN env' a' -> Word
      go (IxN w) = w
  pretty (Symb c) = PP.viaShow c
  -- fromString (show c)
  pretty (SymbI cs) = PP.viaShow cs

data Prod c env a where
  PNil :: !a -> Prod c env a
  PCons :: !(Symb c env b) -> !(Prod c env (b -> a)) -> Prod c env a

instance Functor (Prod c env) where
  fmap f (PNil a) = PNil (f a)
  fmap f (PCons c p) = PCons c (fmap (f .) p)

fromSymb :: Symb c env a -> Prod c env a
fromSymb s = PCons s (PNil id)

instance Applicative (Prod c env) where
  pure = PNil
  (<*>) = go id
    where
      -- Derived from the following definition.
      -- PNil a <*> f = fmap a f
      -- PCons a as <*> r = PCons a (flip <$> as <*> r)
      go :: (a -> b -> r) -> Prod c env a -> Prod c env b -> Prod c env r
      go f (PNil a) r = fmap (f a) r
      go f (PCons a as) r = PCons a (go (flip . (f .)) as r)

instance (Show c) => PP.Pretty (Prod c env a) where
  pretty (PNil _) = fromString "<EMPTY>"
  pretty (PCons s r) = go (PP.pretty s) r
    where
      go :: forall b ann. PP.Doc ann -> Prod c env b -> PP.Doc ann
      go d (PNil _) = d
      go d (PCons ss rr) = d PP.<+> go (PP.pretty ss) rr

newtype RHS c env a = MkRHS {getProds :: [Prod c env a]}

instance Functor (RHS c env) where
  fmap :: forall a b. (a -> b) -> RHS c env a -> RHS c env b
  fmap f =
    coerce
      @([Prod c env a] -> [Prod c env b])
      @(RHS c env a -> RHS c env b)
      $ map (fmap f)

instance (Show c) => PP.Pretty (RHS c env a) where
  pretty (MkRHS rs) =
    PP.align $ PP.sep $ groupEvery 2 $ groupEvery 4 $ addBarFront $ map PP.pretty rs
    where
      addBarFront [] = []
      addBarFront (d : ds) = d : map (bar <>) ds

      groupEvery n = map (PP.group . PP.sep) . Sp.chunksOf n
      bar = fromString "|" <> PP.space

-- | Type-safe representation of grammars in de Bruijn indices.
data FlatGrammar c a
  = forall env. FlatGrammar !(UE.Env (RHS c env) env) !(RHS c env a)

instance (Show c) => PP.Pretty (FlatGrammar c a) where
  pretty (FlatGrammar UE.ENil r) =
    PP.align $ PP.pretty r
  pretty (FlatGrammar bs r) =
    PP.align $
      PP.align (PP.pretty r)
        <> PP.nest 2 (PP.hardline <> fromString "where")
        <> PP.nest 4 (PP.hardline <> PP.vsep (pprDefs bs))
    where
      --    PP.align $ PP.vsep (pprDefs bs) <> PP.line <> pprDefN (fromString "Start") r

      pprDefs :: UE.Env (RHS c env) as -> [PP.Doc ann]
      pprDefs = go 0
        where
          go :: Int -> UE.Env (RHS c env) as -> [PP.Doc ann]
          go _ UE.ENil = mempty
          go n (UE.ECons e es) = pprDef (show n) e : go (n + 1) es

      pprDef x rhs =
        fromString ("N" ++ x)
          PP.<+> PP.group (PP.align (fromString "::=" PP.<+> PP.pretty rhs))

-- pprDefN n rhs = PP.hsep [n, fromString "::=", PP.align (PP.pretty rhs)]
