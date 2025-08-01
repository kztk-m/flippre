{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use section" #-}

import Control.DeepSeq
import Data.String (fromString)
import System.CPUTime

import Prettyprinter (Doc)

import Data.Int (Int8)
import Text.FliPpr hiding (Exp)
import qualified Text.FliPpr as F
import qualified Text.FliPpr.Automaton as A
import qualified Text.FliPpr.Grammar as G
import Text.FliPpr.Grammar.Driver.Earley as Earley
import Text.FliPpr.Implicit (Materializable, define)

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

op s d1 d2 = group $ d1 <> nest 2 (line' <> text s <+>. d2)

opPrinterI :: (Ord k, Num k, Materializable (i1 -> i2 -> d), DocLike d)
   => Fixity -> (d -> d -> d) -> (k -> i1 -> d) -> (k -> i2 -> d) -> k -> i1 -> i2 -> d
opPrinterI (Fixity a opPrec) opD ppr1 ppr2 =
  let (dl, dr) = case a of
        AssocL -> (0, 1)
        AssocR -> (1, 0)
        AssocN -> (0, 0)
      withoutP = define $ \e1 e2 -> opD (ppr1 (fromIntegral opPrec + dl) e1) (ppr2 (fromIntegral opPrec + dr) e2)
      withP = define $ \e1 e2 -> parens (withoutP e1 e2)
  in  \k -> if k > fromIntegral opPrec then withP else withoutP

pprAdd :: Fin Nat4 -> In v Exp -> In v Exp -> F.Exp Implicit v D
pprAdd = define $ \k -> if k > 1 then withP else withoutP 
  where 
    withoutP = define $ \e1 e2 -> op "+" (pprExp 1 e1) (pprExp 2 e2)
    withP    = define $ \e1 e2 -> parens (withoutP e1 e2) 

pprSub :: Fin Nat4 -> In v Exp -> In v Exp -> F.Exp Implicit v D
pprSub = opPrinterI (Fixity AssocL 1) (op "-") pprExp pprExp 

pprMul :: Fin Nat4 -> In v Exp -> In v Exp -> F.Exp Implicit v D
pprMul = define $ opPrinterI (Fixity AssocL 2) (op "*") pprExp pprExp

pprDiv :: Fin Nat4 -> In v Exp -> In v Exp -> F.Exp Implicit v D
pprDiv = define $ \k -> opPrinterI (Fixity AssocL 2) (op "/") pprExp pprExp k

pprLet :: Bool -> In v [Char] -> In v Exp -> In v Exp -> F.Exp Implicit v D
pprLet = \b -> if b then withP else withoutP
  where
    withoutP = define $ \x e1 e2 ->
      sep
        [ hsep [text "let", pprVar x, text "=", nest 2 (line' <> pprExp 0 e1)]
        , hsep [text "in", align $ pprExp 0 e2]
        ]
    withP = define $ \x e1 e2 -> parens (withoutP x e1 e2)

pprExp :: Fin Nat4 -> In v Exp -> F.Exp Implicit v D
pprExp = define $ \k e ->
  manyParens $
    case_
      e
      [ unNum pprInt
      , unVar pprVar
      , unAdd $ \e1 e2 -> pprAdd k e1 e2
      , unSub $ \e1 e2 -> pprSub k e1 e2
      , unMul $ \e1 e2 -> pprMul k e1 e2
      , unDiv $ \e1 e2 -> pprDiv k e1 e2
      , unLet $ pprLet (k > 0)
      ]

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