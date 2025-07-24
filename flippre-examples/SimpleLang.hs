{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
-- To suppress warnings caused by TH code.
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-missing-deriving-strategies #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

import Text.FliPpr hiding (Exp)
import qualified Text.FliPpr as F
import qualified Text.FliPpr.Automaton as AM

import qualified Text.FliPpr.Grammar as G
import qualified Text.FliPpr.Grammar.Driver.Earley as E

import qualified Text.FliPpr.QDo as F

import Data.String (fromString)

import Prettyprinter (Doc)
import Text.Printf

newtype Name = Name String
  deriving (Eq, Show)

data Lit
  = LBool Bool
  | LInt Int
  deriving (Eq, Show)

data BinOp = Add | Mul
  deriving (Eq, Show)
data Exp
  = Op BinOp Exp Exp
  | Let Name Exp Exp
  | Literal Lit
  | If Exp Exp Exp
  | Var Name
  deriving (Eq, Show)

$(mkUn ''Name)
$(mkUn ''Exp)
$(mkUn ''Lit)

otherwiseP :: (arg Exp -> exp t) -> Branch arg exp Exp t
otherwiseP = Branch (PartialBij "otherwiseP" Just Just)

itoaBij :: PartialBij Int String
itoaBij = PartialBij "itoa" (Just . show) $ \s ->
  case reads s of
    (n, "") : _ -> pure n
    _ -> Nothing

number :: AM.DFA Char
number = AM.range '0' '9'

numbers :: AM.DFA Char
numbers = AM.plus number

ident :: AM.DFA Char
ident = (small <> AM.star alphaNum) `AM.difference` AM.unions (map fromString keywords)
  where
    small = AM.unions [AM.range 'a' 'z', AM.singleton '_']
    alphaNum = AM.unions [number, small, AM.range 'A' 'Z']

keywords :: [String]
keywords = ["true", "false", "let", "in", "if", "then", "else"]

flipprExp :: (Phased s) => FliPprM s v (In v Exp -> F.Exp s v D)
flipprExp = F.do
  pprName <- share $ \x -> case_ x [unName $ \s -> textAs s ident]
  pprInt <- share $ \n -> convertInput itoaBij n $ \s -> textAs s numbers
  pprBool <- share $ \b -> case_ b [unTrue $ text "true", unFalse $ text "false"]

  let pprLet p n e1 e2 =
        group $
          vsep
            [ hsep [text "let", pprName n <+>. text "=" <+>. align (p 0 e1)]
            , hsep [text "in", align (p 0 e2)]
            ]
  let pprIf p e0 e1 e2 =
        group $
          vsep
            [ hsep [text "if", p 0 e0]
            , hsep [text "then", p 0 e1]
            , hsep [text "else", p 0 e2]
            ]
  let pprOp p (Fixity assoc prec) opS e1 e2 =
        let (dl, dr)
              | AssocL <- assoc = (0, 1)
              | AssocR <- assoc = (1, 0)
              | AssocN <- assoc = (1, 1)
        in  p (fromIntegral prec + dl) e1 <+>. text opS <+>. p (fromIntegral prec + dr) e2

  let pprVar = pprName
  let pprLit l =
        case_
          l
          [ unLBool pprBool
          , unLInt pprInt
          ]

  -- Technique mentioned in http://www.haskellforall.com/2020/11/pretty-print-syntax-trees-with-this-one.html.
  -- A trick is that patterns are intentionally overlapping, so that it can parse ugly string, wihtout <?
  rec pExp <- share $ \(prec :: Fin Nat5) x ->
        if
          | prec == 0 ->
              case_
                x
                [ unLet $ \n e1 e2 -> pprLet pExp n e1 e2
                , unIf $ \e0 e1 e2 -> pprIf pExp e0 e1 e2
                , otherwiseP $ pExp (prec + 1)
                ]
          | prec == 1 ->
              case_
                x
                [ $(pat 'Op) $(pat 'Add) varP varP `br` \e1 e2 -> pprOp pExp (Fixity AssocL 1) "+" e1 e2
                , otherwiseP $ pExp (prec + 1)
                ]
          | prec == 2 ->
              case_
                x
                [ --  $(branch [p| Op Mul e1 e2 |] [| pprOp pExp (Fixity AssocL 2)  "*" e1 e2 |]),
                  -- compostional approach to pattern matching
                  br ($(pat 'Op) $(pat 'Mul) varP varP) $ \e1 e2 -> pprOp pExp (Fixity AssocL 2) "*" e1 e2
                , otherwiseP $ pExp (prec + 1)
                ]
          | otherwise ->
              case_
                x
                [ unVar $ \n -> pprVar n
                , unLiteral $ \l -> pprLit l
                , otherwiseP $ parens . pExp 0
                ]
  pure (pExp 0)

gExp :: (G.GrammarD Char g) => g (Err ann Exp)
gExp = parsingModeWith (CommentSpec (Just "--") (Just $ BlockCommentSpec "{-" "-}" True)) (flippr $ fromFunction <$> flipprExp :: FliPpr Explicit (Exp ~> D))

parseExp :: [Char] -> Exp
parseExp = \s -> case p s of
  Ok r -> head r
  Fail e -> error (show e)
  where
    -- This assignment is important; otherwise, gExp is evaluated again for calls of parseExp.
    p = E.parse gExp

pprExp :: Exp -> Doc ann
pprExp = pprMode (flippr @Implicit $ fromFunction <$> flipprExp)

exp1 :: Exp
exp1 =
  Let x (Op Mul (Literal $ LInt 5) (Op Add (Literal $ LInt 3) (Literal $ LInt 4))) $
    Let y (If (Literal $ LBool True) (Literal $ LBool False) (Literal $ LBool False)) $
      If (Var y) (Var x) (Literal $ LInt 0)
  where
    x = Name "x"
    y = Name "y"

main :: IO ()
main = do
  let s = show (pprExp exp1)
  putStrLn "`pprExp exp1` results in ..."
  putStrLn s
  let e = parseExp s
  putStrLn $ replicate 80 '-'
  putStrLn "`parseExp (pprExp exp1)` results in ..."
  print e
  putStrLn $ replicate 80 '-'
  printf "`exp1 == parseExp (pprExp exp1)` = %s\n" (show $ e == exp1)
