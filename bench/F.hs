{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecursiveDo #-}

import Text.FliPpr
import Text.FliPpr.Doc
import Text.FliPpr.TH

import qualified Text.FliPpr.Internal.GrammarST as G 
import Text.FliPpr.Driver.Earley (Earley(..))

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
  putStrLn "------------------------------"
  let g0 = G.inline $ G.removeNonProductive $ G.optSpaces g
  print $ G.thawSpace (G.finalize $ return $ fmap (const ()) $ G.text " ") $ g0             
