{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

import Data.String (fromString)
import Data.Word (Word8)
import Debug.Trace (trace)
import qualified Prettyprinter as PP (Doc)

import Text.FliPpr hiding (Exp)
import qualified Text.FliPpr as F
import qualified Text.FliPpr.Automaton as AM
import qualified Text.FliPpr.Grammar as G
import qualified Text.FliPpr.Grammar.Driver.Earley as E
import qualified Text.FliPpr.QDo as F

newtype Name = Name String
  deriving stock (Eq, Show)

data Lit
  = LBool Bool
  | LInt Int
  deriving stock (Eq, Show)

data BinOp = Add | Sub | Mul | Div
  deriving stock (Eq, Show)

data Exp
  = Op BinOp Exp Exp
  | Let Name Exp Exp
  | Literal Lit
  | If Exp Exp Exp
  | App Exp Exp
  | Abs Name Exp
  | Var Name
  deriving stock (Eq, Show)

$(mkUn ''Name)
$(mkUn ''Exp)
$(mkUn ''Lit)

-- When it is true, "\x -> e", "if e then e1 else e2", "let x = e1 in e2" can
-- come without parentheses.
newtype IsRightMost = IsRightMost {isRightMost :: Bool}

deriving via (Bool -> a) instance (RecArg f a) => RecArg f (IsRightMost -> a)

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

pprExp :: (Phased s) => FliPprM s v (In v Exp -> F.Exp s v D)
pprExp = F.do
  pprName <- share $ \x -> case_ x [unName $ \s -> textAs s ident]
  pprInt <- share $ \n -> convertInput itoaBij n $ \s -> textAs s numbers
  pprBool <- share $ \b -> case_ b [unTrue $ text "true", unFalse $ text "false"]

  let pprLet p x e1 e2 =
        sep
          [ hsep [text "let", pprName x <+>. text "=" <+>. align (p 0 (IsRightMost True) e1)]
          , hsep [text "in", align (p 0 (IsRightMost True) e2)]
          ]
  let pprIf p e0 e1 e2 =
        group $
          vsep
            [ hsep [text "if", align $ p 0 (IsRightMost True) e0]
            , hsep [text "then", align $ p 0 (IsRightMost True) e1]
            , hsep [text "else", align $ p 0 (IsRightMost True) e2]
            ]
  let pprAbs p x e =
        nest 2 $
          sep
            [ text "\\" <> pprName x <+>. text "->"
            , align $ p 0 (IsRightMost True) e
            ]

  let pprOp p b (Fixity assoc prec) opS e1 e2 =
        let (dl, dr)
              | AssocL <- assoc = (0, 1)
              | AssocR <- assoc = (1, 0)
              | AssocN <- assoc = (1, 1)
        in  p (fromIntegral prec + dl) (IsRightMost False) e1 <+>. text opS <+>. p (fromIntegral prec + dr) b e2

  let pprApp p b e1 e2 =
        p 10 (IsRightMost False) e1 <+> p 11 b e2

  let pprLit l =
        case_
          l
          [ unLBool pprBool
          , unLInt pprInt
          ]

  rec pExp <- share $ \(prec :: Word8) (b :: IsRightMost) x ->
        if
          -- \| prec == 0 || isRightMost b ->
          --     case_
          --       x
          --       [ unLet $ pprLet pExp
          --       , unIf $ pprIf pExp
          --       , unAbs $ pprAbs pExp
          --       , otherwiseP $ pExp (prec + 1) b
          --       ]
          | prec == 4 ->
              case_
                x
                [ $(pat 'Op) $(pat 'Add) varP varP `br` \e1 e2 -> pprOp pExp b (Fixity AssocL 4) "+" e1 e2
                , $(pat 'Op) $(pat 'Sub) varP varP `br` \e1 e2 -> pprOp pExp b (Fixity AssocL 4) "-" e1 e2
                , otherwiseP $ pExp (prec + 1) b
                ]
          | prec == 6 ->
              case_
                x
                [ $(pat 'Op) $(pat 'Mul) varP varP `br` \e1 e2 -> pprOp pExp b (Fixity AssocL 6) "*" e1 e2
                , $(pat 'Op) $(pat 'Div) varP varP `br` \e1 e2 -> pprOp pExp b (Fixity AssocL 6) "/" e1 e2
                , otherwiseP $ pExp (prec + 1) b
                ]
          | prec == 10 ->
              case_
                x
                [ unApp $ pprApp pExp b
                , otherwiseP $ pExp (prec + 1) b
                ]
          | prec >= 11 ->
              pSimpleExp b x
          | otherwise ->
              pExp (prec + 1) b x
      pSimpleExp <- share $ \b e0 ->
        let
          br0 =
            [ unLet $ \x e1 e2 -> pprLet pExp x e1 e2
            , unIf $ \e e1 e2 -> pprIf pExp e e1 e2
            , unAbs $ \x e -> pprAbs pExp x e
            ]
          br1 =
            [ unVar pprName
            , unLiteral pprLit
            , otherwiseP $ parens . pExp 0 (IsRightMost True)
            ]
        in
          case_ e0 (if isRightMost b then br0 ++ br1 else br1)
  pure $ pExp 0 (IsRightMost True)

pretty :: Exp -> PP.Doc ann
pretty = pprMode (flippr @Explicit $ arg <$> pprExp)

parser :: String -> [Exp]
parser s = case p s of
  Ok es -> es
  Fail e -> error (show e)
  where
    g :: (G.GrammarD Char g) => g (Err ann Exp)
    g = parsingMode (flippr $ arg <$> pprExp :: FliPpr Explicit (Exp ~> D))
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
