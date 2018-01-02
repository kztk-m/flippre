{-# LANGUAGE RecursiveDo #-}

import Text.FliPpr.Internal.GrammarST as G
import Control.Applicative (Alternative(..))
       
_example1 :: Grammar ExChar ()
_example1 = finalize $ do
  rec p <- share $
           text "(" *> p <* text ")" <* p
           <|> pure ()
  return p 


_example2 :: Grammar ExChar [ExChar]
_example2 = finalize $ do
  rec alpha     <- share $ foldr1 (<|>) $ map char ['a'..'z']
      alphas    <- share $ (:) <$> alpha <*> alphaStar
      alphaStar <- share $ pure [] <|> alphas
  return alphas 

_example3 :: Grammar ExChar [ExChar]
_example3 = finalize $ do
  rec alphas    <- do
        alpha     <- share $ foldr1 (<|>) $ map char ['a'..'z']
        alphaStar <- share $ pure [] <|> alphas
        share $ (:) <$> alpha <*> alphaStar
  return alphas



_example4 :: Grammar ExChar ()
_example4 = finalize $ do
  rec alphas <- do 
        alpha     <- share $ foldr1 (<|>) $ map char ['a'..'z']
        alphaStar <- share $ pure [] <|> alphas
        share $ (:) <$> alpha <*> alphaStar
  rec tree    <- share $ pure () <* alphas <* spaces <* text "[" <* spaces <* forest <* spaces <* text "]"
      forest  <- share $ pure () <|> forest1 
      forest1 <- share $
                 tree
                 <|> tree *> spaces <* text "," <* spaces <* forest1
  return tree 
  
main :: IO ()
main = do
  print (G.removeNonProductive $ optSpaces $ _example4) 
