{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RebindableSyntax          #-}
{-# LANGUAGE RecursiveDo               #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeOperators             #-}

-- To suppress warnings caused by TH code.
{-# LANGUAGE MonoLocalBinds            #-}


import           Prelude
import           Text.FliPpr
import           Text.FliPpr.Driver.Earley as Earley
import qualified Text.FliPpr.Grammar       as G

mfix :: LetArg (E f) a => (a -> FliPprM f a) -> FliPprM f a
mfix = mfixF

example1 :: FliPpr ([Bool] ~> D)
example1 = flippr $ do
  let manyParens d = local $ do
        rec m <- share $ d <? parens m
        return m

  pprTF <- define $ \i ->
    manyParens $
      case_
        i
        [ $(un 'True) $ text "True",
          $(un 'False) $ text "False"
        ]

  rec ppr <- define $ \x ->
        manyParens $
          case_
            x
            [ unNil $ text "[" <> text "]",
              unCons $ \a x' -> brackets (ppr' a x')
            ]
      ppr' <- define $ \a x ->
        case_
          x
          [ $(un '[]) $ pprTF a,
            $(branch [p|b : y|] [|pprTF a <> text "," <+>. ppr' b y|])
          ]
  return (fromFunction ppr)

gsp :: G.GrammarD Char g => g ()
gsp = () <$ G.text " "


main :: IO ()
main = do
  let s = "[True,   False, True, (False ), ( (True))  ]"
  let g = parsingModeSP gsp example1
  print $ G.pprGrammar g
  print $ G.pprAsFlat  g
  putStrLn $ replicate 80 '-'
  putStrLn $ "String to be parsed: " ++ show s
  putStrLn "Parse result:"
  print $ Earley.parse g  s
