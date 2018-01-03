{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecursiveDo #-}

import Text.FliPpr
import Text.FliPpr.Doc
import Text.FliPpr.TH

import qualified Text.FliPpr.Internal.GrammarST as G 

example1 :: FliPpr ([Bool] :~> D)
example1 = flippr $ do
  let manyParens d = local $ do
        rec m <- share $ d <? parens m
        return m

  pprTF <- share $ arg $ \i -> manyParens $ case_ i
    [ $(un 'True)  $ text "True",
      $(un 'False) $ text "False" ]

  rec ppr <- share $ arg $ \x -> manyParens $ case_ x
        [ $(un '[]) $ text "[" <> text "]",
          $(branch [p| a:x' |] [| brackets (ppr' `app` a `app` x') |]) ]
      ppr' <- share $ arg $ \a -> arg $ \x -> case_ x
        [ $(un '[]) $ pprTF @@ a,
          $(branch [p| b:y |] [| pprTF `app` a <> text "," <+>. ppr' `app` b `app` y |]) ]
  return ppr
    
main :: IO ()
main = do
  let g = parsingMode example1
  print $ g
  putStrLn "------------------------------"
  print $ G.inline $ G.removeNonProductive $ G.optSpaces g
