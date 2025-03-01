{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TemplateHaskell #-}

module Literals (
    Literal (..),
    IntLit (..),
    FloatLit (..),
    digit,
    pprLit,
) where

import Data.Word (Word64)
import Numeric (showHex, showOct)
import Text.FliPpr
import qualified Text.FliPpr.Automaton as AM
import Prelude

-- Code for defining the automata for int literals
-- would be much nicer if we could just use regex here (like in most other parser generators)
decimalNum :: AM.DFA Char
decimalNum = AM.union (AM.range '1' '9' <> AM.star (AM.range '0' '9')) (AM.singleton '0')

hexNum :: AM.DFA Char
hexNum = AM.plus $ AM.unions [AM.range 'A' 'F', AM.range 'a' 'f', AM.range '0' '9']

octalNum :: AM.DFA Char
octalNum = AM.plus $ AM.range '0' '7'

data IntLit = Int Word64 | UInt Word64 | LInt Word64 | ULInt Word64
    deriving (Show, Eq)

$(mkUn ''IntLit)

-- Int Printer
pprInt :: (FliPprD a e) => FliPprM e (A a IntLit -> E e D)
pprInt = do
    u <- share $ text "u" <? text "U"
    l <- share $ text "l" <? text "L"
    decInt <- share $ \x -> case_ x [atoi $ \s -> textAs s decimalNum]
    hexInt <- share $ \x -> (text "0x" <? text "0X") <#> case_ x [atoiHex $ \s -> textAs s hexNum]
    octInt <- share $ \x -> text "0" <#> case_ x [atoiOct $ \s -> textAs s octalNum]
    int <- share $ \x -> decInt x <? hexInt x <? octInt x
    return $ \x ->
        case_
            x
            [ unInt int
            , unLInt $ \i -> int i <#> l
            , unUInt $ \i -> int i <#> u
            , unULInt $ \i -> int i <#> u <#> l
            ]
  where
    atoi = Branch $ PartialBij "atoi" (Just . show) (Just . read)
    atoiHex = Branch $ PartialBij "atoiHex" (Just . \x -> showHex x "") (\x -> Just $ read $ "0x" ++ x)
    atoiOct = Branch $ PartialBij "atoiOct" (Just . \x -> showOct x "") (\x -> Just $ read $ "0o" ++ x)

data FloatLit = Float Double | Double Double | LDouble Double
    deriving (Show, Eq)

$(mkUn ''FloatLit)

doubleBase :: AM.DFA Char
doubleBase =
    AM.union (AM.singleton '.' <> AM.plus digit) $
        AM.plus digit <> AM.singleton '.' <> AM.star digit

digit :: AM.DFA Char
digit = AM.range '0' '9'

doubleExponent :: AM.DFA Char
doubleExponent =
    AM.union (AM.singleton 'e') (AM.singleton 'E')
        <> AM.plus digit

doubleNum :: AM.DFA Char
doubleNum =
    AM.unions
        [ doubleBase <> doubleExponent -- a double is either a number with a decimal point and opt. exponent
        , doubleBase
        , AM.plus (AM.range '0' '9') <> doubleExponent -- or a number with an exponent
        ]

-- C floats can end or begin with ., which is invalid in haskell
-- so this case cannot be handled through haskell's read directly
readFloat :: String -> Double
readFloat = read . addTrailingZeroes . addBeginningZeroes
  where
    addBeginningZeroes ('.' : xs) = '0' : '.' : xs
    addBeginningZeroes xs = xs
    addTrailingZeroes ['.'] = ".0"
    addTrailingZeroes ('.' : 'e' : xs) = ".0e" ++ xs
    addTrailingZeroes ('.' : 'E' : xs) = ".0e" ++ xs
    addTrailingZeroes (x : xs) = x : addTrailingZeroes xs
    addTrailingZeroes [] = ""

pprFloat :: (FliPprD a e) => FliPprM e (A a FloatLit -> E e D)
pprFloat = do
    doubleExp <- share $ \x -> case_ x [atof $ \s -> textAs s doubleNum]
    floatExp <- share $ \x -> doubleExp x <> (text "F" <? text "f")
    ldoubleExp <- share $ \x -> doubleExp x <> (text "L" <? text "l")
    let float f = case_ f [unDouble doubleExp, unFloat floatExp, unLDouble ldoubleExp]
    return float
  where
    atof = Branch (PartialBij "atof" (Just . show) (Just . readFloat))

data Literal = IntL IntLit | FloatL FloatLit | String String | Char String -- Char is a string in order to represent the specific escape sequence (in accordance with the grammar I am using)
    deriving (Show, Eq)

$(mkUn ''Literal)

stringContents :: AM.DFA Char
stringContents = AM.star $ AM.union (AM.singleton '\\' <> AM.singleton '"') (AM.difference (AM.range ' ' '~') (AM.singleton '"'))

charContents :: AM.DFA Char
charContents = AM.star $ AM.union (AM.singleton '\\' <> AM.singleton '\'') (AM.difference (AM.range ' ' '~') (AM.singleton '\''))

pprLit :: (FliPprD a e) => FliPprM e (A a Literal -> E e D)
pprLit = do
    int <- pprInt
    float <- pprFloat
    string <- share $ \x -> text "\"" <> textAs x stringContents <> text "\""
    char <- share $ \x -> text "'" <> textAs x charContents <> text "'"
    return $ \x ->
        case_
            x
            [ unIntL int
            , unFloatL float
            , unString string
            , unChar char
            ]