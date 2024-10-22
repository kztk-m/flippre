{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE RebindableSyntax          #-}
{-# LANGUAGE RecursiveDo               #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeOperators             #-}

-- To suppress warnings caused by TH code.
{-# LANGUAGE MonoLocalBinds            #-}


import           Control.DeepSeq
import           Prelude
import           System.CPUTime
import           Text.FliPpr
import           Text.FliPpr.Driver.Earley as Earley
import qualified Text.FliPpr.Grammar       as G

import           Data.String               (fromString)

import qualified Text.FliPpr.Automaton     as Automaton


-- import           Debug.Trace


mfix :: Arg (E f) a => (a -> FliPprM f a) -> FliPprM f a
mfix = mfixF

ifThenElse :: Bool -> p -> p -> p
ifThenElse True t _  = t
ifThenElse False _ f = f

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

mkPprInt :: FliPprD a e => FliPprM e (A a Int -> E e D)
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

mkPprVar :: FliPprD a e => FliPprM e (A a String -> E e D)
mkPprVar =
  share $ \x -> textAs x ident
  where
    smallAlpha = Automaton.range 'a' 'z'
    alphaNum = Automaton.unions [Automaton.range '0' '9', Automaton.range 'a' 'z', Automaton.range 'A' 'Z']
    ident = smallAlpha <> Automaton.star alphaNum `Automaton.difference` Automaton.unions (map fromString keywords)

{-# ANN opP "HLint: ignore Avoid lambda using `infix`" #-}

opP :: (DocLike d, Num n, Ord n) => Fixity -> (d -> d -> d) -> (n -> a -> d) -> (n -> b -> d) -> n -> a -> b -> d
opP fixity f p1 p2 k x y = opPrinter fixity f (\k' -> p1 k' x) (\k' -> p2 k' y) k

manyParens :: FliPprD a e => E e D -> E e D
manyParens d = local $ do
  rec x <- define $ d <? parens x
  return x

pExp :: FliPprD arg exp => FliPprM exp (A arg Exp -> E exp D)
pExp = do
  pprInt <- mkPprInt
  pprVar <- mkPprVar
  let op s d1 d2 =
        group $
          d1 <> nest 2 (line' <> text s <+>. d2)
  rec pprE <- define $ \k e ->
        manyParens $
          case_
            e
            [ unNum pprInt,
              unVar pprVar,
              unSub $ opP (Fixity AssocL 1) (op "-") pprE pprE k,
              unAdd $ opP (Fixity AssocL 1) (op "+") pprE pprE k,
              unDiv $ opP (Fixity AssocL 2) (op "/") pprE pprE k,
              unMul $ opP (Fixity AssocL 2) (op "*") pprE pprE k,
              unLet $ \x e1 e2 ->
                parensIf (k > 0) $
                  group $
                    text "let" <+> pprVar x <> text "="
                      <> nest 2 (line' <> pprE 0 e1)
                      <> line
                      <> text "in" <+> pprE 0 e2
            ]
  return (\x -> spaces <> pprE (0 :: FinNE Nat4) x <> spaces)

grammar :: G.GrammarD Char g => g (Err Exp)
grammar = parsingModeWith (CommentSpec Nothing (Just (BlockCommentSpec "/*" "*/" False))) (flippr $ fromFunction <$> pExp)

-- makeParser :: In t => (forall a e. FliPprD a e => FliPprM e (A a t -> E e D)) -> String -> Err [t]
-- makeParser p =
--   Earley.parse $ parsingModeWith (CommentSpec Nothing (Just (BlockCommentSpec "/*" "*/" False))) (flippr $ fromFunction <$> p)

pprExp :: Exp -> Doc
pprExp = pprMode (flippr $ fromFunction <$> pExp)

parseExp :: [Char] -> Err [Exp]
parseExp =
  Earley.parse grammar

parseExp' :: [Char] -> [Exp]
parseExp' s = case parseExp s of
  Ok r   -> r
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
    $ take 100 $ cycle [2 .. 21]

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
  -- print $ G.pprAsFlat $ parsingMode $ flippr $ fmap fromFunction $ fromDFA dfaVar
  rnf s1 `seq` countTime "Exp1" $ do
    print (parseExp' s1)
  where
    s1 = show $ pprExp exp1
