-- A variant of Let.hs using the implicit syntax.
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-missing-deriving-strategies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use section" #-}

import Control.DeepSeq
import Data.String (fromString)
import System.CPUTime

import Prettyprinter (Doc)

import Text.FliPpr hiding (Exp)
import qualified Text.FliPpr as F
import qualified Text.FliPpr.Automaton as A
import qualified Text.FliPpr.Grammar as G
import Text.FliPpr.Grammar.Driver.Earley as Earley
import Text.FliPpr.Implicit (define)

type Name = String

data Exp
  = Add Exp Exp
  | Mul Exp Exp
  | Sub Exp Exp
  | Div Exp Exp
  | Num Int
  | Var Name
  | Let Name Exp Exp
  deriving (Eq, Show)

$(mkUn ''Exp)

keywords :: [String]
keywords = ["let", "in"]

pprInt :: In v Int -> F.Exp Implicit v D
pprInt = define $ \x ->
  case_ x [itoa $ \s -> textAs s numbers]
  where
    numbers = A.plus (A.range '0' '9')
    itoa = Branch (PartialBij "itoa" (Just . show) (\x -> Just (read x :: Int)))

pprVar :: In v [Char] -> F.Exp Implicit v D
pprVar = define $ \s -> textAs s ident
  where
    smallAlpha = A.range 'a' 'z'
    alphaNum = A.unions [A.range '0' '9', A.range 'a' 'z', A.range 'A' 'Z']
    ident = smallAlpha <> A.star alphaNum `A.difference` A.unions (map fromString keywords)

manyParens :: F.Exp Implicit v D -> F.Exp Implicit v D
manyParens d =
  let x = define $ d <? parens x
  in  x

pprExp :: Fin Nat4 -> In v Exp -> F.Exp Implicit v D
pprExp = define $ \k e ->
  manyParens $
    case_
      e
      [ unNum pprInt
      , unVar pprVar
      , unAdd $ \e1 e2 ->
          opPrinter
            (Fixity AssocL 1)
            (op "+")
            (flip pprExp e1)
            (flip pprExp e2)
            k
      , unSub $ \e1 e2 ->
          opPrinter
            (Fixity AssocL 1)
            (op "-")
            (flip pprExp e1)
            (flip pprExp e2)
            k
      , unMul $ \e1 e2 ->
          opPrinter
            (Fixity AssocL 2)
            (op "*")
            (flip pprExp e1)
            (flip pprExp e2)
            k
      , unDiv $ \e1 e2 ->
          opPrinter
            (Fixity AssocL 2)
            (op "/")
            (flip pprExp e1)
            (flip pprExp e2)
            k
      , unLet $ \x e1 e2 ->
          parensIf (k > 0) $
            sep
              [ hsep [text "let", pprVar x, text "=", nest 2 (line' <> pprExp 0 e1)]
              , hsep [text "in", align $ pprExp 0 e2]
              ]
      ]
  where
    op s d1 d2 = group $ d1 <> nest 2 (line' <> text s <+>. d2)

grammar :: (G.GrammarD Char g) => g (Err ann Exp)
grammar = parsingModeWith (CommentSpec Nothing (Just (BlockCommentSpec "/*" "*/" False))) (FliPpr $ fromFunction $ pprExp 0)

prettyExp :: Exp -> Doc ann
prettyExp = pprMode (FliPpr $ fromFunction $ pprExp 0)

parseExp :: String -> Err ann [Exp]
parseExp = Earley.parse grammar

parseExp' :: String -> [Exp]
parseExp' s = case parseExp s of
  Ok r -> r
  Fail e -> error (show e)

exp1 :: Exp
exp1 =
  foldl
    ( \r x ->
        if x `mod` 4 == 0
          then Mul r (Num $ x `div` 4)
          else
            if x `mod` 4 == 1
              then Add r (Num $ x `div` 4)
              else
                if x `mod` 4 == 2
                  then Let "x" (Num $ x `div` 4) r
                  else Let "x" r (Var "x")
    )
    (Num 0)
    $ take 100
    $ cycle [2 .. 21]

countTime :: String -> IO a -> IO a
countTime str comp = do
  putStrLn $ "Measuring " ++ str ++ "..."
  s <- getCPUTime
  r <- comp
  e <- getCPUTime
  let d = fromIntegral (e - s) / (1000000000 :: Double)
  putStrLn $ "Elapsed: " ++ show d ++ " msec."
  return r

main :: IO ()
main = do
  print (parseExp' "1 + 1")
  print $ G.pprAsFlat grammar
  -- print $ G.pprAsFlat $ parsingMode $ flippr $ fmap fromFunction $ fromDFA dfaVar
  rnf s1 `seq` countTime "Exp1" $ do
    print (parseExp' s1)
  where
    s1 = show $ prettyExp exp1