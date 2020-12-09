{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecursiveDo           #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}

module Text.FliPpr.Driver.Earley (asEarley, parse) where

import           Data.Foldable            (asum)
import qualified Data.RangeSet.List       as RS
import qualified Text.Earley              as E
import           Text.FliPpr.Doc          as D
import           Text.FliPpr.Err
import qualified Text.FliPpr.Grammar      as G
import qualified Text.FliPpr.Internal.Env as Env

toEarley :: Ord c => G.FlatGrammar c a -> E.Grammar r (E.Prod r c c a)
toEarley (G.FlatGrammar defs rhs) = do
  rec env <- Env.traverseWithVar (const $ procRHS env) defs
  procRHS env rhs
  where
    procRHS :: Ord c => Env.Env Env.U (E.Prod r c c) env -> G.RHS c env t -> E.Grammar r (E.Prod r c c t)
    procRHS env (G.RHS ps) = do
      xs <- mapM (procProd env) ps
      E.rule (asum xs)

    procProd :: Ord c => Env.Env Env.U (E.Prod r c c) env -> G.Prod c env a -> E.Grammar r (E.Prod r c c a)
    procProd _env (G.PNil a) = return (pure a)
    procProd env (G.PCons s r) = do
      s' <- procSymb env s
      r' <- procProd env r
      return $ (\a k -> k a) <$> s' <*> r'

    procSymb :: Ord c => Env.Env Env.U (E.Prod r c c) env -> G.Symb c env a -> E.Grammar r (E.Prod r c c a)
    procSymb _env (G.Symb c)   = pure $ E.namedToken c
    procSymb _env (G.SymbI cs) = pure $ E.satisfy (`RS.member` cs)
    procSymb env (G.NT x)      = pure $ Env.lookupEnv x env

asEarley :: Ord c => G.ToFlatGrammar c t -> E.Grammar r (E.Prod r c c t)
asEarley g = toEarley $ G.flatten g

parse :: forall c a. (Show c, Ord c) => (forall g. G.GrammarD c g => g (Err a)) -> [c] -> Err [a]
parse g = \str ->
  case E.fullParses pp str of
    (as@(_ : _), _) -> sequence as
    ([], E.Report i es v) ->
      err $
        D.hsep
          [ D.text "Error: parse error",
            D.align $
              D.vsep
                [ D.text "at position" <+> ppr i,
                  D.text "expecting:" <+> D.text (show es),
                  D.text "near:" <+> D.text (show v)
                ]
          ]
  where
    gr :: E.Grammar r (E.Prod r c c (Err a))
    gr = asEarley g
    pp :: E.Parser c [c] (Err a)
    pp = E.parser gr
