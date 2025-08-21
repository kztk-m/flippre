{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- {-# OPTIONS_GHC -Wno-unused-top-binds #-}

import Text.FliPpr hiding (Exp)
import qualified Text.FliPpr as F
import qualified Text.FliPpr.Automaton as AM

import qualified Text.FliPpr.Grammar as G
import qualified Text.FliPpr.Grammar.Driver.Earley as E

import Text.FliPpr.Implicit
import qualified Text.FliPpr.QDo as F

import Data.String (fromString)

import Data.Proxy (Proxy (..))
import Data.Word (Word8)
import Debug.Trace (trace)
import GHC.Generics (Generic)
import qualified Prettyprinter as PP (Doc)

newtype Name = Name String
  deriving stock (Eq, Show, Generic)

data Lit
  = LBool Bool
  | LInt Int
  deriving stock (Eq, Show, Generic)

data BinOp = Add | Sub | Mul | Div
  deriving stock (Eq, Show, Generic)
data Exp
  = Op BinOp Exp Exp
  | Let Name Exp Exp
  | Literal Lit
  | If Exp Exp Exp
  | App Exp Exp
  | Abs Name Exp
  | Var Name
  deriving stock (Eq, Show, Generic)

instance Destructable Name
instance Destructable Lit
instance Destructable BinOp
instance Destructable Exp

$(mkUn ''Exp)

pattern Name_ i <- i
{-# COMPLETE Name_ #-}

pattern LBool_ b <- Left b
pattern LInt_ i <- Right i

{-# COMPLETE LBool_, LInt_ #-}

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

pprName :: In v Name -> F.Exp Implicit v D
pprName = define $ \n -> match @Name n $ \case
  Name_ s -> textAs s ident

pprInt :: In v Int -> F.Exp Implicit v D
pprInt = define $ \n -> convertInput itoaBij n $ \s ->
  textAs s numbers

pprBool :: In v Bool -> F.Exp Implicit v D
pprBool = define $ \b -> match @Bool b $ \case
  True -> text "true"
  False -> text "false"

newtype IsRightMost = IsRightMost {isRightMost :: Bool}

deriving via
  Bool -> b
  instance
    (Materializable b) => Materializable (IsRightMost -> b)

-- instance (Arg m a) => Arg m (IsRightMost -> a) where
--   letr = G.letrVia (Proxy :: Proxy (Bool -> a))

pprLet :: In v Name -> In v Exp -> In v Exp -> F.Exp Implicit v D
pprLet = define $ \x e1 e2 ->
  sep
    [ hsep [text "let", pprName x <+>. text "=" <+>. align (pprExp 0 (IsRightMost True) e1)]
    , hsep [text "in", align (pprExp (0 :: Int) (IsRightMost True) e2)]
    ]
pprIf :: In v Exp -> In v Exp -> In v Exp -> F.Exp Implicit v D
pprIf = define $ \e0 e1 e2 ->
  sep
    [ hsep [text "if", align $ pprExp 0 (IsRightMost True) e0]
    , hsep [text "then", align $ pprExp 0 (IsRightMost True) e1]
    , hsep [text "else", align $ pprExp 0 (IsRightMost True) e2]
    ]

pprAbs :: In v Name -> In v Exp -> F.Exp Implicit v D
pprAbs = define $ \x e ->
  nest 2 $
    sep
      [ text "\\" <> pprName x <+>. text "->"
      , align $ pprExp 0 (IsRightMost True) e
      ]

pprApp :: IsRightMost -> In v Exp -> In v Exp -> F.Exp Implicit v D
pprApp = define $ \b e1 e2 -> pprExp 10 (IsRightMost False) e1 <+> pprExp 11 b e2

pprLit :: In v Lit -> F.Exp Implicit v D
pprLit = define $ \l -> match @Lit l $ \case
  LBool_ b -> pprBool b
  LInt_ i -> pprInt i

pprOp :: Fixity -> String -> IsRightMost -> In v Exp -> In v Exp -> F.Exp Implicit v D
pprOp (Fixity assoc prec) opS = define $ \b e1 e2 ->
  let (dl, dr)
        | AssocL <- assoc = (0, 1)
        | AssocR <- assoc = (1, 0)
        | AssocN <- assoc = (1, 1)
  in  pprExp (fromIntegral prec + dl) (IsRightMost False) e1 <+>. text opS <+>. pprExp (fromIntegral prec + dr) b e2

pprExp :: Int -> IsRightMost -> In v Exp -> F.Exp Implicit v D
pprExp = define $ \prec b e ->
  if
    | prec == 4 ->
        case_
          e
          [ $(pat 'Op) $(pat 'Add) varP varP `br` \e1 e2 -> pprOp (Fixity AssocL 4) "+" b e1 e2
          , $(pat 'Op) $(pat 'Sub) varP varP `br` \e1 e2 -> pprOp (Fixity AssocL 4) "-" b e1 e2
          , otherwiseP $ pprExp (prec + 1) b
          ]
    | prec == 6 ->
        case_
          e
          [ $(pat 'Op) $(pat 'Mul) varP varP `br` \e1 e2 -> pprOp (Fixity AssocL 6) "*" b e1 e2
          , $(pat 'Op) $(pat 'Div) varP varP `br` \e1 e2 -> pprOp (Fixity AssocL 6) "/" b e1 e2
          , otherwiseP $ pprExp (prec + 1) b
          ]
    | prec == 10 ->
        case_
          e
          [ $(pat 'App) varP varP `br` pprApp b
          , otherwiseP $ pprExp (prec + 1) b
          ]
    | prec >= 11 ->
        pprSimpleExp b e
    | otherwise ->
        pprExp (prec + 1) b e

pprSimpleExp :: IsRightMost -> In v Exp -> F.Exp Implicit v D
pprSimpleExp = define $ \b e0 ->
  let
    br0 =
      [ unLet $ \x e1 e2 -> pprLet x e1 e2
      , unIf $ \e e1 e2 -> pprIf e e1 e2
      , unAbs $ \x e -> pprAbs x e
      ]
    br1 =
      [ unVar pprName
      , unLiteral pprLit
      , otherwiseP $ parens . pprExp 0 (IsRightMost True)
      ]
  in
    case_ e0 (if isRightMost b then br0 ++ br1 else br1)

pretty :: Exp -> PP.Doc ann
pretty = pprMode (FliPpr $ arg $ pprExp 0 (IsRightMost True))

parser :: String -> [Exp]
parser s = case p s of
  Ok es -> es
  Fail e -> error (show e)
  where
    g :: (G.GrammarD Char g) => g (Err ann Exp)
    g = parsingMode (FliPpr $ arg $ pprExp 0 (IsRightMost True))
    p = trace (show $ G.pprAsFlat g) $ E.parse g

checkRoundTrip :: String -> IO ()
checkRoundTrip s = do
  putStrLn $ "Checking parse s = e ==> parse (pretty e) = e for s = " ++ show s
  case parser s of
    [e] -> do
      let s' = show (pretty e)
      putStrLn $ "Pretty-printed reslut:"
      putStrLn s'
      case parser s' of
        [e']
          | e == e' -> putStrLn "ok."
          | otherwise -> do
              putStrLn "Parse result mismatch"
              putStrLn $ "Expected: " ++ show e
              putStrLn $ "Obtained: " ++ show e'
        [] -> putStrLn $ "Parse failed for s'"
        es' ->
          putStrLn $ "Multiple parse results for s'" ++ show es'
    [] ->
      putStrLn $ "Parse failed"
    es -> putStrLn $ "Multiple parse results" ++ show es

main :: IO ()
main = do
  checkRoundTrip "1 + let x = 2 in x * 3"
  checkRoundTrip "\\x -> \\y -> \\z -> x z (y z)"
  checkRoundTrip "(\\x -> x x) (\\x -> x x)"
  checkRoundTrip "1 + let x = f let y = 1 in 1 in x * 3"