{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Text.FliPpr

import qualified Text.FliPpr.Grammar as G
import qualified Text.FliPpr.Grammar.Driver.Earley as E

import qualified Text.FliPpr.Automaton as AM

-- RebindableSyntax
import Text.FliPpr.Mfix
import Prelude

ident :: AM.DFA Char
ident = small <> AM.star alphaNum
  where
    number = AM.range '0' '9'
    small = AM.unions [AM.range 'a' 'z', AM.singleton '_']
    alphaNum = AM.unions [number, small, AM.range 'A' 'Z']

repeats :: (FliPprD a e) => (E e D -> E e D -> E e D) -> (E e D -> E e D -> E e D) -> FliPprM e (E e ([String] ~> D))
repeats op1 op2 = do
  ptext <- define $ \i -> textAs i ident
  rec p <- define $ \i -> case_ i [unNil $ text "", unCons $ \x xs -> p' x xs]
      p' <- define $ \x xs -> case_ xs [unNil $ ptext x, unCons $ \y ys -> ptext x `op1` text "," `op2` p' y ys]
  pure $ arg p

main :: IO ()
main = do
  let str = "a  ,  bb  ,   ccc    ,    dddd"
  print $ E.parse (parsingMode $ flippr $ repeats (<>) (<>)) str
  putStrLn "---"
  print $ E.parse (parsingMode $ flippr $ repeats (<>) (<+>)) str
  putStrLn "---"
  print $ E.parse (parsingMode $ flippr $ repeats (<>) (\x y -> x <+> text "" <> y)) str
  putStrLn "---"
  print $ E.parse (parsingMode $ flippr $ repeats (<>) (\x y -> x <+> text "" <+> y)) str
