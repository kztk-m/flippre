{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}

-- To suppress warnings caused by TH code.
{-# LANGUAGE MonoLocalBinds            #-}


import           Prelude
import           Data.Word (Word64)
import           Numeric (showHex, showOct)
import           Text.FliPpr
import           Text.FliPpr.Grammar.Driver.Earley as E
import qualified Text.FliPpr.Automaton     as AM
import Prettyprinter (Doc, pretty)


-- Code for defining the automata for int literals
-- would be much nicer if we could just use regex here (like in most other parser generators)
decimalNum :: AM.DFA Char
decimalNum = AM.range '1' '9' <> AM.star (AM.range '0' '9')

hexNum :: AM.DFA Char
hexNum = AM.plus $ AM.unions [AM.range 'A' 'F',  AM.range 'a' 'f', AM.range '0' '9']

octalNum :: AM.DFA Char
octalNum = AM.star $ AM.range '0' '7'

data IntLit = Int Word64 | UInt Word64 | LInt Word64 | ULInt Word64
            deriving (Show, Eq)

$(mkUn ''IntLit)

-- Int Printer
pprInt :: FliPprD a e => FliPprM e (A a IntLit -> E e D)
pprInt = do
  u <- define $ text "u" <? text "U"
  l <- define $ text "l" <? text "L"
  decInt   <- define $ \x -> case_ x [atoi $ \s -> textAs s decimalNum]
  hexInt   <- define $ \x -> (text "0x" <? text "0X") <> case_ x [atoiHex $ \s -> textAs s hexNum]
  octInt   <- define $ \x -> text "0" <> case_ x [atoiOct $ \s -> textAs s octalNum]
  int      <- define $ \x -> decInt x <? hexInt x <? octInt x
  return $ \x -> case_ x [ unInt int
                         , unLInt $ \i -> int i <#> l
                         , unUInt $ \i -> int i  <#> u
                         , unULInt $ \i -> int i <#> u <#> l
                         ]
  where
    atoi    = Branch $ PartialBij "atoi" (Just . show) (Just . read)
    atoiHex = Branch $ PartialBij "atoiHex" (Just . \x -> showHex x "") (\x -> Just $ read $ "0x" ++ x)
    atoiOct = Branch $ PartialBij "atoiOct" (Just . \x -> showOct x "") (\x -> Just $ read $ "0o" ++ x)

data FloatLit = Float Double | Double Double | LDouble Double
              deriving (Show, Eq)

$(mkUn ''FloatLit)

doubleBase :: AM.DFA Char
doubleBase = AM.union (AM.singleton '.' <> AM.plus digit)
                      $ AM.plus digit <> AM.singleton '.' <> AM.star digit

digit :: AM.DFA Char
digit = AM.range '0' '9'

doubleExponent :: AM.DFA Char
doubleExponent = AM.union (AM.singleton 'e') (AM.singleton 'E')
                          <> AM.plus digit

doubleNum :: AM.DFA Char
doubleNum = AM.unions [ doubleBase <> doubleExponent -- a double is either a number with a decimal point and opt. exponent
                      , doubleBase
                      , AM.plus (AM.range '0' '9') <> doubleExponent  ] -- or a number with an exponent

-- C floats can end or begin with ., which is invalid in haskell
-- so this case cannot be handled through haskell's read directly
readFloat :: String -> Double
readFloat = read . addTrailingZeroes . addBeginningZeroes
  where
    addBeginningZeroes ('.':xs) = '0' : '.' : xs
    addBeginningZeroes xs = xs
    addTrailingZeroes ['.'] = ".0"
    addTrailingZeroes ('.':'e':xs) = ".0e" ++ xs
    addTrailingZeroes ('.':'E':xs) = ".0e" ++ xs
    addTrailingZeroes (x:xs) = x : addTrailingZeroes xs
    addTrailingZeroes [] = ""

pprFloat :: FliPprD a e => FliPprM e (A a FloatLit -> E e D)
pprFloat = do
  doubleExp <- define $ \x -> case_ x [atof $ \s -> textAs s doubleNum]
  floatExp  <- define $ \x -> doubleExp x <> (text "F" <? text "f")
  ldoubleExp <- define $ \x -> doubleExp x <> (text "L" <? text "l")
  let float f = case_ f [ unDouble doubleExp, unFloat floatExp, unLDouble ldoubleExp ]
  return float
  where
    atof = Branch (PartialBij "atof" (Just . show) (Just . readFloat))

data Literal = IntL IntLit | FloatL FloatLit -- missing: Char, String
             deriving (Show, Eq)

$(mkUn ''Literal)

pprLit :: FliPprD a e => FliPprM e (A a Literal -> E e D)
pprLit = do
  int <- pprInt
  float <- pprFloat
  return $ \x -> case_ x [ unIntL int
                         , unFloatL float
                         ]

data Exp = LitExp Literal | IdentExp String | FunctionCall String [Exp]
          deriving (Show, Eq)

$(mkUn ''Exp)

ident :: AM.DFA Char
ident = AM.unions [AM.range 'A' 'z', AM.singleton '_']
      <> AM.star (AM.unions [AM.range 'A' 'z', digit, AM.singleton '_'])


pprExp :: FliPprD a e => FliPprM e (A a Exp -> E e D)
pprExp = do
  lit <- pprLit
  identExp <- define $ \x -> textAs x ident
  let pExp l = case_ l [ unLitExp lit
                       , unIdentExp identExp
                       , unFunctionCall $ \f args ->
                          let argList a = case_ a [ unNil $ text ""
                                                  , unCons $ \x xs -> pExp x <> case_ xs
                                                      [ unNil $ text ""
                                                      , unCons $ \_ _ -> text "," <+>. argList xs ] -- lookahead to see if comma is needed
                                                  ]
                          in identExp f <> text "(" <> argList args <> text ")"
                       ]
  return pExp

exp1 :: Exp
exp1 = FunctionCall "f" [LitExp $ IntL $ Int 42, LitExp $ FloatL $ Float 3.14, FunctionCall "g" []]

pprProgram :: Exp -> Doc ann
pprProgram = pprMode (flippr $ fromFunction <$> pprExp)

parseProgram :: [Char] -> Err ann [Exp]
parseProgram = E.parse $ parsingMode (flippr $ fromFunction <$> pprExp)