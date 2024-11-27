{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
-- To suppress warnings caused by TH code.
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Text.FliPpr
import qualified Text.FliPpr.Grammar as G
import Text.FliPpr.Grammar.Driver.Earley as Earley
import Prelude

-- for RebindableSyntax (used with RecursiveDo)
import Control.Applicative ((<|>))
import Text.FliPpr.Mfix (mfix)

manyParens :: (FliPprD arg exp) => E exp D -> E exp D
manyParens d = local $ do
  rec m <- share $ d <? parens m
  return m

defPprTF :: (FliPprD arg exp) => FliPprM exp (A arg Bool -> E exp D)
defPprTF = define $ \i ->
  manyParens $
    case_
      i
      [ $(un 'True) $ text "True"
      , $(un 'False) $ text "False"
      ]

example1 :: FliPpr ([Bool] ~> D)
example1 = flippr $ do
  pprTF <- defPprTF

  rec ppr <- define $ \x ->
        manyParens $
          case_
            x
            [ unNil $ text "[" <> text "]"
            , unCons $ \a x' -> brackets (ppr' a x')
            ]
      ppr' <- define $ \a x ->
        case_
          x
          [ $(un '[]) $ pprTF a
          , $(branch [p|b : y|] [|pprTF a <> text "," <+>. ppr' b y|])
          ]
  return (fromFunction ppr)

example2 :: FliPpr ([Bool] ~> D)
example2 = flippr $ do
  pprTF <- defPprTF
  pure $ arg $ brackets . foldPprL (\a d -> pprTF a <> text "," <+>. d) pprTF (text "")

gsp :: (G.GrammarD Char g) => g ()
gsp = () <$ (G.text " " <|> G.text "\n")

main :: IO ()
main = do
  let s = "[True,   False, True, (False ), ( (True))  ]"
  let g :: (G.GrammarD Char g) => g (Err ann [Bool])
      g = parsingModeSP gsp example1
  print $ G.pprGrammar @Char g
  print $ G.pprAsFlat g
  putStrLn $ replicate 80 '-'
  putStrLn $ "String to be parsed: " ++ show s
  putStrLn "Parse result:"
  print $ Earley.parse g s
  putStrLn $ replicate 80 '='
  let g' = parsingModeSP gsp example2
  print $ G.pprGrammar g'
  print $ G.pprAsFlat g'
  putStrLn $ "String to be parsed: " ++ show s
  putStrLn "Parse result:"
  print $ Earley.parse g' s
