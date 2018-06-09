{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecursiveDo #-}

import Text.FliPpr

import qualified Text.FliPpr.Internal.GrammarST as G 
import Text.FliPpr.Driver.Earley (Earley(..))

example1 :: FliPpr ([Bool] :~> D)
example1 = flippr $ do
  let manyParens d = local $ do
        rec m <- share $ d <? parens m
        return m
        
  pprTF <- define $ \i -> manyParens $ case_ i
    [ $(un 'True)  $ text "True",
      $(un 'False) $ text "False" ]

  rec ppr <- define $ \x -> manyParens $ case_ x
        [ unNil  $ text "[" <> text "]",
          unCons $ \a x' -> brackets (ppr' a x') ]
      ppr' <- define $ \a x -> case_ x
        [ $(un '[]) $ pprTF a,
          $(branch [p| b:y |] [| pprTF a <> text "," <+>. ppr' b y |]) ]
  return (fromFunction ppr)

gsp :: G.Grammar Char ()
gsp = G.finalize $ return $ fmap (const ()) $ G.text " " 

gram1 :: G.Grammar Char (Err [Bool])
gram1 = parsingModeSP gsp example1
  where
    gsp = G.finalize $ return $ fmap (const ()) $ G.text " "

parser1 :: String -> Err [[Bool]]
parser1 = G.parse Earley gram1

example2 :: FliPpr ([Bool] :~> D)
example2 = flippr $ do
  pprTF <- share $ arg $ \x -> case_ x
    [ $(un 'True) $ text "True",
      $(un 'False) $ text "False" ]

  rec ppr <- share $ arg $ \x -> case_ x
        [ $(un '[]) $ text "",
          $(un '(:)) $ \a y -> app pprTF a <> app ppr y ]

  return ppr 
  
    
main :: IO ()
main = do
  let g = parsingMode example1
  print $ g
