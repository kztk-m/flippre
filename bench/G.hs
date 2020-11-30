{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}

-- import Text.FliPpr.Internal.GrammarST as G

import Control.Applicative (Alternative (..))
import Data.Foldable (asum)
import Text.FliPpr.Grammar as G
import Prelude

_example1 :: GrammarD ExChar g => g ()
_example1 = G.local $ do
  rec p <-
        G.rule $
          text "(" *> G.nt p <* text ")" <* G.nt p
            <|> pure ()
  return $ G.nt p
  where
    mfix = G.mfixDefM

_example2 :: GrammarD ExChar g => g [ExChar]
_example2 = G.local $ do
  rec alpha <- G.rule $ foldr1 (<|>) $ map char ['a' .. 'z']
      alphas <- G.rule $ (:) <$> G.nt alpha <*> G.nt alphaStar
      alphaStar <- G.rule $ pure [] <|> G.nt alphas
  return $ G.nt alphas
  where
    mfix = G.mfixDefM

-- _example3 :: Grammar ExChar g => g [ExChar]
-- _example3 = runDefM $ do
--   rec alphas <- do
--         alpha <- share $ foldr1 (<|>) $ map symb ['a' .. 'z']
--         alphaStar <- share $ pure [] <|> alphas
--         share $ (:) <$> alpha <*> alphaStar
--   return alphas

-- _example4 :: Grammar ExChar g => g ()
-- _example4 = runDefM $ do
--   rec alphas <- do
--         alpha <- share $ foldr1 (<|>) $ map symb ['a' .. 'z']
--         alphaStar <- share $ pure [] <|> alphas
--         share $ (:) <$> alpha <*> alphaStar
--   rec tree <- share $ pure () <* alphas <* spaces <* text "[" <* spaces <* forest <* spaces <* text "]"
--       forest <- share $ pure () <|> forest1
--       forest1 <-
--         share $
--           tree
--             <|> tree *> spaces <* text "," <* spaces <* forest1
--   return tree

main :: IO ()
main = do
  print $ G.pprGrammar _example2
  putStrLn "--- after simplification ---"
  print $ G.pprGrammar $ G.simplifyGrammar _example2
  putStrLn "--- after manipulation of spaces ---"
  print (G.pprGrammar $ G.withSpace (simplifyGrammar $ () <$ asum (map G.symb " \t\r\n")) $ G.simplifyGrammar $ _example2)
