{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Text.FliPpr

import qualified Text.FliPpr.Internal.GrammarST as G 
import Text.FliPpr.Driver.Earley (Earley(..))
import Data.Maybe (fromJust)
import Data.List ((\\))

import Control.DeepSeq
import Debug.Trace

import System.CPUTime


type Name = String 

data Exp = Add Exp Exp
         | Mul Exp Exp
         | Sub Exp Exp
         | Div Exp Exp
         | Num Int
         | Var Name
         | Let Name Exp Exp 
         deriving (Eq , Show)

$(mkUn ''Exp) 

type Q = Int
data DFA = DFA { init :: Q, trans :: [(Q, [(Char,Q)])], finals :: [Q] }


fromDFA :: FliPprD m a e => DFA -> m (A a String -> E e D)
fromDFA (DFA init tr fs) = do
  rec abort <- define abort
  rec f <- defines (map fst tr) $ \q s -> case_ s $
--        [unNil $ (if elem q fs then text " " else abort),
--        (if elem q fs then ((unNil $ text ""):) else id)
        [ unNil $ (if elem q fs then text " " else abort),
          unCons $ \a r -> case_ a
          [is c $ text [c] <#> (f q' r) |
            (c, q') <- fromJust (lookup q tr) ]]
  return (f init) 


dfaNum :: DFA 
dfaNum = DFA 0 [ (0, [ (c, 2) | c <- digit ] ++ [ ('-', 1) ] ),
                 (1, [ (c, 2) | c <- digit ]),
                 (2, [ (c, 2) | c <- digit ]) ] [2]
  where
    digit = ['0'..'9']
    

dfaVar :: DFA
dfaVar = DFA 0 [ (0, [ (c, 1) | c <- smallAlpha \\ ['l'] ] ++ [('l', 2)]),
                 (1, [ (c, 1) | c <- alphaNum ]),
                 (2, [ (c, 1) | c <- alphaNum \\ ['e'] ] ++ [('e',3)] ),
                 (3, [ (c, 1) | c <- alphaNum \\ ['t'] ] ++ [('t',4)] ),
                 (4, [ (c, 1) | c <- alphaNum ]) ] [1,2,3]
  where
    smallAlpha = ['a'..'z']
    alphaNum   = ['0'..'9'] ++ ['a'..'z'] ++ ['A'..'Z']

mkPprInt :: FliPprD m a e => m (A a Int -> E e D)
mkPprInt = do f <- fromDFA dfaNum
              return $ \x -> case_ x [atoi $ f ]
  where
    atoi = Branch (PartialBij "atoi" (Just . show) (\x -> Just (read x :: Int)))

mkPprVar :: FliPprD m a e => m (A a String -> E e D)
mkPprVar = fromDFA dfaVar 


opP :: DocLike d => Fixity -> (d -> d -> d) -> (Prec -> a -> d) -> (Prec -> b -> d) -> Prec -> a -> b -> d 
opP fixity f p1 p2 k x y = opPrinter fixity f (\k -> p1 k x) (\k -> p2 k y) k


manyParens :: FliPprD m a e => E e D -> E e D 
manyParens d = local $ do 
  rec x <- define $ d <? parens x 
  return x 
  
pExp :: FliPprD m arg exp => m (A arg Exp -> E exp 'D)
pExp = do
  pprInt <- mkPprInt
  pprVar <- mkPprVar
  let op s d1 d2 = group $
        d1 <> nest 2 (line' <> text s <+>. d2)
  rec pprE <- defines [0..3] $ \k e -> manyParens $ case_ e
        [ unNum $ pprInt,
          unVar $ pprVar,
          unSub $ opP (Fixity AssocL 1) (op "-") pprE pprE k, 
          unAdd $ opP (Fixity AssocL 1) (op "+") pprE pprE k, 
          unDiv $ opP (Fixity AssocL 2) (op "/") pprE pprE k, 
          unMul $ opP (Fixity AssocL 2) (op "*") pprE pprE k,
          unLet $ \x e1 e2 -> parensIf (k > 0) $ group $
            text "let" <+> pprVar x <> text "=" <>
              nest 2 (line' <> pprE 0 e1) <>
            line <> text "in" <+> pprE 0 e2 ]
  return (\x -> spaces <> pprE 0 x <> spaces)

grammar :: Grammar Char (Err Exp)
grammar = parsingModeWith (CommentSpec Nothing (Just (BlockCommentSpec "/*" "*/" False))) (flippr $ fromFunction <$> pExp)

makeParser :: In t => (forall m a e. FliPprD m a e => m (A a t -> E e D)) -> String -> Err [t] 
makeParser p =
  G.parse Earley $ parsingModeWith (CommentSpec Nothing (Just (BlockCommentSpec "/*" "*/" False))) (flippr $ fromFunction <$> p)

pprExp :: Exp -> Doc
pprExp = pprMode (flippr $ fromFunction <$> pExp) 

parseExp :: [Char] -> Err [Exp]
parseExp =
  G.parse Earley grammar 

parseExp' :: [Char] -> [Exp]
parseExp' s = case parseExp s of
                Ok   s -> s
                Fail s -> error (show s) 

exp1 :: Exp
exp1 = foldl (\r x ->
                if x `mod` 4 == 0 then
                  Mul r (Num $ x `div` 4)
                else if x `mod` 4 == 1 then
                       Add r (Num $ x `div` 4)
                     else if x `mod` 4 == 2 then 
                       Let "x" (Num $ x `div` 4) r
                          else
                            Let "x" r (Var "x")
             ) (Num 0)
       $ take 100 $ cycle [2..21]

              
countTime :: String -> IO a -> IO a
countTime str comp = do
  putStrLn $ "Measuring " ++ str ++ "..."
  s <- getCPUTime
  r <- comp
  e <- getCPUTime
  let d = (fromIntegral $ e - s) / (1000000000 :: Double) 
  putStrLn $ "Elapsed: " ++ show d ++ " msec."
  return r 

main :: IO ()
main = do  
  rnf s1 `seq` countTime "Exp1" $ do     
    print (parseExp' s1)
  where
    s1 = show $ pprExp exp1
