{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

-- import Text.FliPpr.Internal.GrammarST as G

import Control.Applicative (Alternative (..))
import Data.Foldable (asum)
import Text.FliPpr.Grammar as G
import qualified Text.FliPpr.Grammar.UnFlatten as G
import Prelude

_example1 :: (GrammarD ExChar g) => g ()
_example1 = G.local $ do
  rec p <-
        G.rule $
          text "("
            *> G.nt p
            <* text ")"
            <* G.nt p
              <|> pure ()
  return $ G.nt p
  where
    mfix = G.mfixDefM

_example2 :: (GrammarD ExChar g) => g [ExChar]
_example2 = G.local $ do
  rec alpha <- G.rule $ foldr1 (<|>) $ map char ['a' .. 'z']
      alphas <- G.rule $ (:) <$> G.nt alpha <*> G.nt alphaStar
      alphaStar <- G.rule $ pure [] <|> G.nt alphas
  return $ G.nt alphas
  where
    mfix = G.mfixDefM

_example3 :: (GrammarD ExChar g) => g [ExChar]
_example3 = G.local $ do
  rec alphas <- do
        alpha <- G.rule $ foldr1 (<|>) $ map char ['a' .. 'z']
        alphaStar <- G.rule $ pure [] <|> G.nt alphas
        G.rule $ (:) <$> G.nt alpha <*> G.nt alphaStar
  return $ G.nt alphas
  where
    mfix = G.mfixDefM

_example4 :: (GrammarD ExChar g) => g ()
_example4 = G.local $ do
  rec alphas <- do
        alpha <- G.rule $ foldr1 (<|>) $ map char ['a' .. 'z']
        alphaStar <- G.rule $ pure [] <|> G.nt alphas
        G.rule $ (:) <$> G.nt alpha <*> G.nt alphaStar
  rec tree <- G.rule $ () <$ G.nt alphas <* spaces <* text "[" <* spaces <* G.nt forest <* spaces <* text "]"
      forest <- G.rule $ pure () <|> G.nt forest1
      forest1 <- G.rule $ G.nt tree <|> G.nt tree *> spaces <* text "," <* spaces <* G.nt forest1
  return $ G.nt tree
  where
    mfix = G.mfixDefM

main :: IO ()
main = do
  let ex = _example4
  print $ G.pprAsFlat ex

  let ex' = G.simplify ex
  putStrLn "--- after simplification ---"
  print $ G.pprAsFlat ex'

  let ex'' = G.withSpace (G.simplify $ () <$ asum (map G.symb " \t\r\n")) ex'

  putStrLn "--- after manipulation of spaces ---"
  print $ G.pprAsFlat ex''

  putStrLn "--- further simplification ---"
  print $ G.pprAsFlat $ G.simplify ex''
