{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- | Interpretation of 'Grammar's as Earley parsers.
module Text.FliPpr.Grammar.Driver.Earley (asEarley, parse) where

import Data.Foldable (asum)
import qualified Data.RangeSet.List as RS
import qualified Text.Earley as E

import qualified Text.FliPpr.Grammar as G
import Text.FliPpr.Grammar.Err

import Data.String (IsString (..))
import qualified Prettyprinter as PP
import Text.FliPpr.Grammar.Internal.Util (traverseEnvWithIx)

toEarley :: (Ord c) => G.FlatGrammar c a -> E.Grammar r (E.Prod r c c a)
toEarley (G.FlatGrammar defs rhs) = do
  rec env <- traverseEnvWithIx (const $ procRHS env) defs
  procRHS env rhs
  where
    procRHS :: (Ord c) => G.Env (E.Prod r c c) env -> G.RHS c env t -> E.Grammar r (E.Prod r c c t)
    procRHS env (G.MkRHS ps) = do
      xs <- mapM (procProd env) ps
      E.rule (asum xs)

    procProd :: (Ord c) => G.Env (E.Prod r c c) env -> G.Prod c env a -> E.Grammar r (E.Prod r c c a)
    procProd _env (G.PNil a) = return (pure a)
    procProd env (G.PCons s r) = do
      s' <- procSymb env s
      r' <- procProd env r
      return $ (\a k -> k a) <$> s' <*> r'

    procSymb :: (Ord c) => G.Env (E.Prod r c c) env -> G.Symb c env a -> E.Grammar r (E.Prod r c c a)
    procSymb _env (G.Symb c) = pure $ E.namedToken c
    procSymb _env (G.SymbI cs) = pure $ E.satisfy (`RS.member` cs)
    procSymb env (G.NT x) = pure $ G.lookEnv env x

-- | Converts our grammars into those in @Text.Earley@.
asEarley :: (Ord c) => (forall g. (G.GrammarD c g) => g t) -> E.Grammar r (E.Prod r c c t)
asEarley g = toEarley $ G.flatten g

-- | Performs parsing after conversion by 'asEarley'.
--
--   There is a caveat in the usage of this function.
--   Merely using @parse g s@ multiple times triggers re-interpretation of @g@. So please prepare a partially applied function as:
--
--   > parseG = parse g
--
--   to avoid the re-interpretatin of g.
parse :: forall c a ann. (Show c, Ord c) => (forall g. (G.GrammarD c g) => g (Err ann a)) -> [c] -> Err ann [a]
parse g = \str ->
  case E.fullParses pp str of
    (as@(_ : _), _) -> sequence as
    ([], E.Report i es v) ->
      err $
        PP.hsep
          [ "Error: parse error"
          , PP.align $
              PP.vsep
                [ "at position" PP.<+> PP.pretty i
                , "expecting:" PP.<+> fromString (show es)
                , "near:" PP.<+> fromString (show v)
                ]
          ]
  where
    gr :: E.Grammar r (E.Prod r c c (Err ann a))
    gr = asEarley g
    pp :: E.Parser c [c] (Err ann a)
    pp = E.parser gr
