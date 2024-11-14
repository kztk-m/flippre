{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE FlexibleContexts #-}

-- To suppress warnings caused by TH code.
{-# LANGUAGE MonoLocalBinds            #-}


import           Prelude
import           Data.Word (Word, Word64)
import           Numeric (showHex, showOct)
import           Text.FliPpr
import           Text.FliPpr.Grammar.Driver.Earley as E
import qualified Text.FliPpr.Automaton     as AM
import Prettyprinter (Doc)


-- Code for defining the automata for int literals
-- would be much nicer if we could just use regex here (like in most other parser generators)
decimalNum :: AM.DFA Char
decimalNum = AM.range '1' '9' <> AM.star (AM.range '0' '9')

hexNum :: AM.DFA Char
hexNum = AM.plus $ AM.unions [AM.range 'A' 'F',  AM.range 'a' 'f', AM.range '0' '9']

octalNum :: AM.DFA Char
octalNum = AM.star $ AM.range '0' '7'

data IntExp = Dec Word64 | UDec Word64 | LDec Word64 | ULDec Word64
            deriving (Show, Eq)

$(mkUn ''IntExp)

-- Int Printer
pprInt :: FliPprD a e => FliPprM e (A a IntExp -> E e D)
pprInt = do
  u <- define $ text "u" <? text "U"
  l <- define $ text "l" <? text "L"
  decInt   <- define $ \x -> case_ x [atoi $ \s -> textAs s decimalNum]
  hexInt   <- define $ \x -> (text "0x" <? text "0X") <> case_ x [atoiHex $ \s -> textAs s hexNum]
  octInt   <- define $ \x -> text "0" <> case_ x [atoiOct $ \s -> textAs s octalNum]
  int      <- define $ \x -> decInt x <? hexInt x <? octInt x
  return $ \x -> case_ x [ unDec int
                         , unLDec $ \i -> int i <#> l
                         , unUDec $ \i -> int i  <#> u
                         , unULDec $ \i -> int i <#> u <#> l
                         ]
  where
    atoi    = Branch $ PartialBij "atoi" (Just . show) (Just . read)
    atoiHex = Branch $ PartialBij "atoiHex" (Just . \x -> showHex x "") (\x -> Just $ read $ "0x" ++ x)
    atoiOct = Branch $ PartialBij "atoiOct" (Just . \x -> showOct x "") (\x -> Just $ read $ "0o" ++ x)

data FloatExp = Float Double | Double Double | LDouble Double
              deriving (Show, Eq)

$(mkUn ''FloatExp)

doubleBase :: AM.DFA Char
doubleBase = AM.union (AM.singleton '.' <> AM.plus digit)
                      $ AM.plus digit <> AM.singleton '.' <> AM.star digit

digit :: AM.DFA Char
digit = AM.range '0' '9'

doubleExponent :: AM.DFA Char
doubleExponent = AM.union (AM.singleton 'e') (AM.singleton 'E')
               <> AM.plus digit

doubleNum :: AM.DFA Char
doubleNum = AM.union (doubleBase <> doubleExponent) -- a double is either a number with a decimal point and opt. exponent
                     (AM.plus (AM.range '0' '9') <> doubleExponent) -- or an integer with an exponent



pprFloat :: FliPprD a e => FliPprM e (A a FloatExp -> E e D)
pprFloat = do
  doubleExp <- define $ \x -> case_ x [atof $ \s -> textAs s doubleExponent]
  floatExp  <- define $ \x -> doubleExp x <> (text "F" <? text "f")
  ldoubleExp <- define $ \x -> doubleExp x <> (text "L" <? text "l")
  let float f = case_ f [ unDouble doubleExp ]
  return float
  where
    atof = Branch (PartialBij "atof" (show) (readFloat))

pprExp :: FloatExp -> Doc ann
pprExp = pprMode (flippr $ fromFunction <$> pprFloat)

parseExp :: [Char] -> Err ann [FloatExp]
parseExp = E.parse $ parsingMode (flippr $ fromFunction <$> pprFloat)