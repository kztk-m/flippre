{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
-- To suppress warnings caused by TH code.
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-missing-deriving-strategies #-}

import Control.DeepSeq
import System.CPUTime
import Text.FliPpr hiding (Exp)
import qualified Text.FliPpr as F
import qualified Text.FliPpr.Grammar as G
import Text.FliPpr.Grammar.Driver.Earley as Earley
import qualified Text.FliPpr.QDo as F
import Prelude

import Data.String (fromString)

import qualified Text.FliPpr.Automaton as Automaton

import Prettyprinter (Doc)

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

mkPprInt :: (Phased s) => FliPprM s v (In v Int -> F.Exp s v D)
mkPprInt =
  share $ \x -> case_ x [atoi $ \s -> textAs s numbers]
  where
    numbers = Automaton.plus (Automaton.range '0' '9')
    atoi = Branch (PartialBij "atoi" (Just . show) (\x -> Just (read x :: Int)))

-- mkPprInt :: FliPprD a e => FliPprM e (A a Int -> E e D)
-- mkPprInt = do
--   f <- fromDFA dfaNum
--   return $ \x -> case_ x [atoi f]
--   where

keywords :: [String]
keywords = ["let", "in"]

mkPprVar :: (Phased s) => FliPprM s v (In v String -> F.Exp s v D)
mkPprVar =
  share $ \x -> textAs x ident
  where
    smallAlpha = Automaton.range 'a' 'z'
    alphaNum = Automaton.unions [Automaton.range '0' '9', Automaton.range 'a' 'z', Automaton.range 'A' 'Z']
    ident = smallAlpha <> Automaton.star alphaNum `Automaton.difference` Automaton.unions (map fromString keywords)

{-# ANN opP "HLint: ignore Avoid lambda using `infix`" #-}
opP :: (DocLike d, Num n, Ord n) => Fixity -> (d -> d -> d) -> (n -> a -> d) -> (n -> b -> d) -> n -> a -> b -> d
opP fixity f p1 p2 k x y = opPrinter fixity f (\k' -> p1 k' x) (\k' -> p2 k' y) k

manyParens :: (Phased s) => F.Exp s v D -> F.Exp s v D
manyParens d = local $ F.do
  rec x <- share $ d <? parens x
  return x

pExp :: (Phased s) => FliPprM s v (In v Exp -> F.Exp s v D)
pExp = F.do
  pprInt <- mkPprInt
  pprVar <- mkPprVar
  let op s d1 d2 =
        group $
          d1 <> nest 2 (line' <> text s <+>. d2)

  let opPr (Fixity a opPrec) opD ppr1 ppr2 = do
        let (dl, dr) = case a of
              AssocL -> (0, 1)
              AssocR -> (1, 0)
              AssocN -> (0, 0)
        withoutP <- share $ \e1 e2 -> opD (ppr1 (fromIntegral opPrec + dl) e1) (ppr2 (fromIntegral opPrec + dr) e2)
        withP <- share $ \e1 e2 -> parens (withoutP e1 e2)
        pure $ \k -> if k > fromIntegral opPrec then withP else withoutP
  rec pprAdd <- opPr (Fixity AssocL 1) (op "+") pprE pprE
      pprSub <- opPr (Fixity AssocL 1) (op "-") pprE pprE
      pprDiv <- opPr (Fixity AssocL 2) (op "/") pprE pprE
      pprMul <- opPr (Fixity AssocL 2) (op "*") pprE pprE
      pprLet <- do
        d1 <- share $ \x e1 e2 ->
          sep
            [ hsep [text "let", pprVar x, text "=", nest 2 (line' <> pprE 0 e1)]
            , hsep [text "in", align $ pprE 0 e2]
            ]
        d2 <- share $ \x e1 e2 -> parens (d1 x e1 e2)
        pure $ \b -> if b then d2 else d1
      pprE <- share $ \(k :: Fin Nat4) e ->
        manyParens $
          case_
            e
            [ unNum pprInt
            , unVar pprVar
            , unSub $ pprSub k
            , unAdd $ pprAdd k
            , unDiv $ pprDiv k
            , unMul $ pprMul k
            , unLet $ pprLet (k > 0)
            ]
  return (\x -> spaces <> pprE (0 :: Fin Nat4) x <> spaces)

grammar :: (G.GrammarD Char g) => g (Err ann Exp)
grammar = parsingModeWith (CommentSpec Nothing (Just (BlockCommentSpec "/*" "*/" False))) (flippr $ fromFunction <$> pExp :: FliPpr Explicit (Exp ~> D))

-- makeParser :: In t => (forall a e. FliPprD a e => FliPprM e (A a t -> E e D)) -> String -> Err [t]
-- makeParser p =
--   Earley.parse $ parsingModeWith (CommentSpec Nothing (Just (BlockCommentSpec "/*" "*/" False))) (flippr $ fromFunction <$> p)

pprExp :: Exp -> Doc ann
pprExp = pprMode (flippr @Explicit $ fromFunction <$> pExp)

parseExp :: [Char] -> Err ann [Exp]
parseExp =
  Earley.parse grammar

parseExp' :: [Char] -> [Exp]
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
  print (flippr @Explicit $ fromFunction <$> pExp)
  print (parseExp' "1 + 1")
  print $ G.pprAsFlat grammar
  rnf s1 `seq` countTime "Exp1" $ do
    print (parseExp' s1)
  where
    s1 = show $ pprExp exp1
