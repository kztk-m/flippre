{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RebindableSyntax          #-}
{-# LANGUAGE RecursiveDo               #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeOperators             #-}

import           Prelude
import           Text.FliPpr
import           Text.FliPpr.Driver.Earley as Earley
import qualified Text.FliPpr.Grammar       as G

mfix = mfixF

example1 :: FliPpr ([Bool] :~> D)
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

gram1 :: G.GrammarD Char g => g (Err [Bool])
gram1 = parsingModeSP gsp example1

parser1 :: String -> Err [[Bool]]
parser1 = Earley.parse gram1

example2 :: FliPpr ([Bool] :~> D)
example2 = flippr $ do
  pprTF <- share $
    arg $ \x ->
      case_
        x
        [ $(un 'True) $ text "True",
          $(un 'False) $ text "False"
        ]

  rec ppr <- share $
        arg $ \x ->
          case_
            x
            [ $(un '[]) $ text "",
              $(un '(:)) $ \a y -> app pprTF a <> app ppr y
            ]

  return ppr

main :: IO ()
main = do
  let g = parsingMode example1
  print $ G.pprAsFlat g
