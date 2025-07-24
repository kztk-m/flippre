{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeApplications #-}
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

-- repeats :: (FliPprD a e) => (E e D -> E e D -> E e D) -> (E e D -> E e D -> E e D) -> FliPprM e (E e ([String] ~> D))
repeats :: (Exp s v D -> Exp s v D -> Exp s v D) -> (Exp s v D -> Exp s v D -> Exp s v D) -> FliPprM s v (Exp s v ([String] ~> D))
repeats op1 op2 = do
  ptext <- share $ \i -> textAs i ident
  rec p <- share $ \i -> case_ i [unNil $ text "", unCons $ \x xs -> p' x xs]
      p' <- share $ \x xs -> case_ xs [unNil $ ptext x, unCons $ \y ys -> ptext x `op1` text "," `op2` p' y ys]
  pure $ arg p

main :: IO ()
main = do
  let str = "a  ,  bb  ,   ccc    ,    dddd"
  print $ E.parse (parsingMode $ flippr @Explicit $ repeats (<>) (<>)) str
  putStrLn "---"
  print $ E.parse (parsingMode $ flippr @Explicit $ repeats (<>) (<+>)) str
  putStrLn "---"
  print $ E.parse (parsingMode $ flippr @Explicit $ repeats (<>) (\x y -> x <+> text "" <> y)) str
  putStrLn "---"
  print $ E.parse (parsingMode $ flippr @Explicit $ repeats (<>) (\x y -> x <+> text "" <+> y)) str
