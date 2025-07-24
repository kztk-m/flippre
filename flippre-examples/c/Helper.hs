{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Helper (
  space',
  list,
  inlineList,
  sepBy,
  sepByNonEmpty,
  manyParens,
  ident,
  otherwiseP,
  NonEmpty (..),
) where

import Data.String (fromString)
import Literals (digit)
import Text.FliPpr
import qualified Text.FliPpr.Automaton as AM
import Text.FliPpr.Grammar (Defs)
import qualified Text.FliPpr.QDo as F
import Prelude

space' :: Exp s v D
space' = text " " <? text ""

otherwiseP :: (arg b -> exp t) -> Branch arg exp b t
otherwiseP = Branch (PartialBij "otherwiseP" Just Just)

data NonEmpty a = NCons a (NonEmpty a) | NNil a
  deriving (Show, Eq)

$(mkUn ''NonEmpty)

list :: (Phased s) => (In v a -> Exp s v D) -> FliPprM s v (In v [a] -> Exp s v D)
list p = F.do
  rec listNE <- share $ \t ts ->
        case_
          ts
          [ unNil $ p t -- singleton case
          , unCons $ \t' ts' -> p t <> line <> listNE t' ts' -- cons case
          ]
      list' <- share $ \ts ->
        case_
          ts
          [ unNil $ text "" -- empty case
          , unCons $ \t' ts' -> listNE t' ts'
          ]
  return list'

inlineList :: (Phased s) => (In v a -> Exp s v D) -> FliPprM s v (In v [a] -> Exp s v D)
inlineList p = F.do
  rec listNE <- share $ \t ts ->
        case_
          ts
          [ unNil $ p t -- singleton case
          , unCons $ \t' ts' -> p t <+> listNE t' ts' -- cons case
          ]
      list' <- share $ \ts ->
        case_
          ts
          [ unNil $ text "" -- empty case
          , unCons $ \t' ts' -> listNE t' ts'
          ]
  return list'

sepBy :: (Phased s) => Exp s v D -> (In v a -> Exp s v D) -> FliPprM s v (In v [a] -> Exp s v D)
sepBy comma p = F.do
  rec commaSepNE <- share $ \x xs ->
        case_
          xs
          [ unNil $ p x
          , unCons $ \t ts -> p x <> comma <> commaSepNE t ts
          ]
  return $ \xs ->
    case_
      xs
      [ unNil $ text ""
      , unCons commaSepNE
      ]

sepByNonEmpty :: (Phased s) => Exp s v D -> (In v a -> Exp s v D) -> FliPprM s v (In v (NonEmpty a) -> Exp s v D)
sepByNonEmpty comma p = F.do
  rec commaSepNE <- share $ \x xs ->
        case_
          xs
          [ unNNil $ \t -> p x <> comma <> p t
          , unNCons $ \t ts -> p x <> comma <> commaSepNE t ts
          ]
  return $ \xs ->
    case_
      xs
      [ unNNil p
      , unNCons commaSepNE
      ]

keywords :: [String]
keywords =
  [ "void"
  , "char"
  , "short"
  , "int"
  , "long"
  , "float"
  , "double"
  , "signed"
  , "unsigned"
  , "const"
  , "volatile"
  , "auto"
  , "register"
  , "static"
  , "extern"
  , "typedef"
  , "struct"
  , "union"
  , "enum"
  , "case"
  , "default"
  , "if"
  , "else"
  , "switch"
  , "while"
  , "do"
  , "for"
  , "goto"
  , "continue"
  , "break"
  , "return"
  ]

ident :: AM.DFA Char
ident =
  ( AM.unions [AM.range 'a' 'z', AM.range 'A' 'Z', AM.singleton '_']
      <> AM.star (AM.unions [AM.range 'a' 'z', AM.range 'A' 'Z', digit, AM.singleton '_'])
  )
    `AM.difference` AM.unions (map fromString keywords)

manyParens :: (Phased s) => Exp s v D -> Exp s v D
manyParens d = local $ F.do
  rec m <- share $ d <? parens m
  return m