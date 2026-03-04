{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -Wno-missing-deriving-strategies #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

import Criterion.Main
import Data.String (fromString)
import Data.Word
import Numeric (showHex, showOct)
import Prettyprinter (Doc)
import Prelude

import Text.FliPpr hiding (Exp)
import qualified Text.FliPpr as F
import qualified Text.FliPpr.Automaton as AM
import Text.FliPpr.Grammar.Driver.Earley as E

-- flattened version of https://github.com/nuernbergk/flippre/blob/239d2b6087e67efd5439c66bbe1e712245f4ec39/flippre-examples/c/C.hs

-- necessary for recursions within do blocks
mfix :: (RecArg (F.Exp s v) a, Phased s) => (a -> FliPprM s v a) -> FliPprM s v a
mfix = mfixF

ifThenElse :: Bool -> t -> t -> t
ifThenElse True t _ = t
ifThenElse False _ f = f

define :: (Applicative f) => a -> f a
define = pure

-- list :: (FliPprD a e, Eq v) => (In  v -> E e D) -> FliPprM e (A a [v] -> E e D)
list :: (Phased s) => (In v a -> F.Exp s v D) -> FliPprM s v (In v [a] -> F.Exp s v D)
list p = do
  rec listNE <- define $ \t ts ->
        case_
          ts
          [ unNil $ p t -- singleton case
          , unCons $ \t' ts' -> p t <+> listNE t' ts' -- cons case
          ]
      list' <- define $ \ts ->
        case_
          ts
          [ unNil $ text "" -- empty case
          , unCons $ \t' ts' -> listNE t' ts'
          ]
  return list'

-- sepBy :: (FliPprD a e, Eq v) => String -> (A a v -> E e D) -> FliPprM e (A a [v] -> E e D)
sepBy :: (Phased s) => String -> (In v a -> F.Exp s v D) -> FliPprM s v (In v [a] -> F.Exp s v D)
sepBy comma p = do
  rec commaSepNE <- define $ \x xs ->
        case_
          xs
          [ unNil $ p x
          , unCons $ \t ts -> p x <> text comma <+>. commaSepNE t ts
          ]
  return $ \xs ->
    case_
      xs
      [ unNil $ text ""
      , unCons commaSepNE
      ]

-- sepByClose :: (FliPprD a e, Eq v) => String -> (A a v -> E e D) -> FliPprM e (A a [v] -> E e D)
sepByClose :: (Phased s) => String -> (In v a -> F.Exp s v D) -> FliPprM s v (In v [a] -> F.Exp s v D)
sepByClose comma p = do
  rec commaSepNE <- define $ \x xs ->
        case_
          xs
          [ unNil $ p x
          , unCons $ \t ts -> p x <> text comma <> commaSepNE t ts
          ]
  return $ \xs ->
    case_
      xs
      [ unCons commaSepNE
      ]

-- commaSep :: (FliPprD a e, Eq v) => (A a v -> E e D) -> FliPprM e (A a [v] -> E e D)
commaSep :: (Phased s) => (In v a -> F.Exp s v D) -> FliPprM s v (In v [a] -> F.Exp s v D)
commaSep = sepBy ","

-- TODO: space if necessary

-- manyParens :: (FliPprE arg exp, Defs exp) => E exp D -> E exp D
manyParens :: (Phased s') => F.Exp s' v D -> F.Exp s' v D
manyParens d = local $ do
  rec m <- define $ d <? parens m
  return m

---

-- Code for defining the automata for int literals
-- would be much nicer if we could just use regex here (like in most other parser generators)
decimalNum :: AM.DFA Char
decimalNum = AM.range '1' '9' <> AM.star (AM.range '0' '9')

hexNum :: AM.DFA Char
hexNum = AM.plus $ AM.unions [AM.range 'A' 'F', AM.range 'a' 'f', AM.range '0' '9']

octalNum :: AM.DFA Char
octalNum = AM.star $ AM.range '0' '7'

data IntLit = Int Word64 | UInt Word64 | LInt Word64 | ULInt Word64
  deriving (Show, Eq)

$(mkUn ''IntLit)

-- Int Printer
-- pprInt :: (FliPprD a e) => FliPprM e (A a IntLit -> E e D)
pprInt :: (Monad m, Phased s) => m (In v IntLit -> F.Exp s v D)
pprInt = do
  u <- define $ text "u" <? text "U"
  l <- define $ text "l" <? text "L"
  decInt <- define $ \x -> case_ x [atoi $ \s -> textAs s decimalNum]
  hexInt <- define $ \x -> (text "0x" <? text "0X") <> case_ x [atoiHex $ \s -> textAs s hexNum]
  octInt <- define $ \x -> text "0" <> case_ x [atoiOct $ \s -> textAs s octalNum]
  int <- define $ \x -> decInt x <? hexInt x <? octInt x
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

-- pprFloat :: (FliPprD a e) => FliPprM e (A a FloatLit -> E e D)
pprFloat :: (Monad m, Phased s) => m (In v FloatLit -> F.Exp s v D)
pprFloat = do
  doubleExp <- define $ \x -> case_ x [atof $ \s -> textAs s doubleNum]
  floatExp <- define $ \x -> doubleExp x <> (text "F" <? text "f")
  ldoubleExp <- define $ \x -> doubleExp x <> (text "L" <? text "l")
  let float f = case_ f [unDouble doubleExp, unFloat floatExp, unLDouble ldoubleExp]
  return float
  where
    atof = Branch (PartialBij "atof" (Just . show) (Just . readFloat))

data Literal = IntL IntLit | FloatL FloatLit -- TODO missing: Char, String
  deriving (Show, Eq)

$(mkUn ''Literal)

-- pprLit :: (FliPprD a e) => FliPprM e (A a Literal -> E e D)
pprLit :: (Monad m, Phased s) => m (In v Literal -> F.Exp s v D)
pprLit = do
  int <- pprInt
  float <- pprFloat
  return $ \x ->
    case_
      x
      [ unIntL int
      , unFloatL float
      ]

----

data Exp = LitExp Literal | IdentExp String | FunctionCall String [Exp]
  deriving (Show, Eq)
$(mkUn ''Exp)

-- type StructDeclList = [(TypeSpecifierQualifier, StructDecl)]

data TypeSpecifier
  = TVoid
  | TChar
  | TShort
  | TInt
  | TLong
  | TFloat
  | TDouble
  | TSigned
  | TUnsigned
  | -- | TStruct String StructDeclList | TAnonStruct StructDeclList -- | TUnion String StructDeclList
    -- | TEnum String
    TName String
  deriving (Show, Eq)

data StorageClass = Auto | Register | Static | Extern | Typedef
  deriving (Show, Eq)

$(mkUn ''StorageClass)

-- pprStorageClass :: (FliPprD a e) => FliPprM e (A a StorageClass -> E e D)
pprStorageClass :: (Applicative f) => f (In v StorageClass -> F.Exp s v D)
pprStorageClass = define $ \x ->
  case_
    x
    [ unAuto $ text "auto"
    , unRegister $ text "register"
    , unStatic $ text "static"
    , unExtern $ text "extern"
    , unTypedef $ text "typedef"
    ]

$(mkUn ''TypeSpecifier)

data TypeQualifier = TConst | TVolatile
  deriving (Show, Eq)

$(mkUn ''TypeQualifier)

data Decl
  = DPointer [Pointer] DirectDecl
  | DirectDecl DirectDecl
  deriving (Show, Eq)

data AbsDirect
  = AbsArray Exp
  | AbsArrayUnsized
  | AbsFunction
  | AbsDecl AbsDecl
  deriving
    ( Show
      -- ^ AbsProto ParamList
    , Eq
    )

data AbsDecl = AbsPointer [Pointer] | AbsPointerDecl [Pointer] [AbsDirect] | AbsDirectDecl [AbsDirect]
  deriving (Show, Eq)

data Parameter = PDecl [DeclSpecifier] Decl | PAbsDecl [DeclSpecifier] AbsDecl | PSpecOnly [DeclSpecifier]
  deriving (Show, Eq)

data DirectDecl
  = DIdent String
  | DArray DirectDecl Exp
  | DArrayUnsized DirectDecl
  | DFunction DirectDecl [String]
  | DDecl Decl
  deriving
    ( Show
      -- ^ DProto DirectDecl ParamList
    , Eq
    )

data Pointer = Pointer [TypeQualifier]
  deriving (Show, Eq)

data DeclSpecifier = DeclStor StorageClass | DeclSpec TypeSpecifier | DeclQual TypeQualifier
  deriving (Show, Eq)

$(mkUn ''Decl)
$(mkUn ''DirectDecl)
$(mkUn ''Pointer)
$(mkUn ''DeclSpecifier)
$(mkUn ''AbsDecl)
$(mkUn ''AbsDirect)
$(mkUn ''Parameter)

data ParamList = Variadic [Parameter] | Fixed [Parameter]
  deriving (Show, Eq)

$(mkUn ''ParamList)

-- pprTypeQualifier :: (FliPprD a e) => FliPprM e (A a TypeQualifier -> E e D)
pprTypeQualifier :: (Applicative f) => f (In v TypeQualifier -> F.Exp s v D)
pprTypeQualifier = define $ \x ->
  case_
    x
    [ unTConst $ text "const"
    , unTVolatile $ text "volatile"
    ]

-- pprPointerList :: (FliPprD a e) => FliPprM e (A a [Pointer] -> E e D)
pprPointerList :: (Phased s) => FliPprM s v (In v [Pointer] -> F.Exp s v D)
pprPointerList = do
  pTypeQualifier <- pprTypeQualifier
  typeQualifierList <- list pTypeQualifier
  pointer <- define $ \p ->
    case_
      p
      [ unPointer $ \qs ->
          text "*"
            <> case_
              qs
              [ unNil $ text ""
              , unCons $ \t ts -> pTypeQualifier t <+> typeQualifierList ts
              ]
              -- TODO: what if non-alphanumeric symbol follows?
      ]
  rec pointerList <- sepByClose "" pointer
  return pointerList

-- pprDecl :: (FliPprD a e) => FliPprM e (A a Decl -> E e D)
pprDecl :: FliPprM Explicit v (In v Decl -> F.Exp Explicit v D)
pprDecl = do
  pExp <- pprExp
  identList <- commaSep (`textAs` ident)
  pointerList <- pprPointerList
  -- pParamList <- pprParamList
  rec pDirectDecl <- define $ \x ->
        case_
          x
          [ unDIdent $ \i -> textAs i ident
          , unDArray $ \d e -> pDirectDecl d <> text "[" <> pExp e <> text "]"
          , unDFunction $ \d args -> pDirectDecl d <> text "(" <> identList args <> text ")"
          , unDArrayUnsized $ \d -> pDirectDecl d <> text "[" <> text "]"
          , unDDecl $ \d -> parens $ pDecl d
          -- , unDProto $ \d ps -> pDirectDecl d <> parens (pParamList ps)
          ]
      pDecl <- define $ \x ->
        case_
          x
          [ unDirectDecl pDirectDecl
          , unDPointer $ \ps d -> pointerList ps <> pDirectDecl d
          ]

  return pDecl

-- pprDeclSpecifier :: (FliPprD a e) => FliPprM e (A a DeclSpecifier -> E e D)
pprDeclSpecifier :: (Phased s1, Phased s2) => FliPprM s1 v1 (In v2 DeclSpecifier -> F.Exp s2 v2 D)
pprDeclSpecifier = do
  pTypeSpecifier <- pprTypeSpec
  pTypeQualifier <- pprTypeQualifier
  pStorageClass <- pprStorageClass
  return $ \x ->
    case_
      x
      [ unDeclStor pStorageClass
      , unDeclSpec pTypeSpecifier
      , unDeclQual pTypeQualifier
      ]

-- pprAbstractDecl :: (FliPprD a e) => FliPprM e (A a AbsDecl -> E e D)
pprAbstractDecl :: FliPprM Explicit v (In v AbsDecl -> F.Exp Explicit v D)
pprAbstractDecl = do
  pExp <- pprExp
  pointerList <- pprPointerList
  -- pParamList <- pprParamList
  rec pDirectDecl <- define $ \x ->
        case_
          x
          [ unAbsArray $ \e -> text "[" <> pExp e <> text "]"
          , unAbsFunction $ parens $ text ""
          , unAbsArrayUnsized $ text "[" <> text "]"
          , unAbsDecl $ \d -> parens $ pDecl d
          -- , unAbsProto $ \ps -> parens $ pParamList ps
          ]
      pDirectDeclList <- define $ \ds ->
        case_
          ds
          [ unNil $ text ""
          , unCons $ \d ds' -> pDirectDecl d <> pDirectDeclList ds'
          ]
      pDecl <- define $ \x ->
        case_
          x
          [ unAbsDirectDecl $ \ds -> pDirectDeclList ds
          , unAbsPointerDecl $ \ps ds -> pointerList ps <> pDirectDeclList ds
          , unAbsPointer $ \ps -> pointerList ps
          ]
  return pDecl

-- helpPrint = putStrLn . unlines . map (show . pprProgram')

expDecl :: Decl
expDecl = DPointer [Pointer [TConst, TVolatile]] $ DArrayUnsized $ DIdent "x"

-- pprTypeSpec :: (FliPprD a e) => FliPprM e (A a TypeSpecifier -> E e D)
-- pprTypeSpec :: Phased s => FliPprM s v (In v TypeSpecifier -> F.Exp s v D)
pprTypeSpec = do
  pExp <- pprExp
  -- structDecl <- define $ \t ->
  -- struct <- define $ \name decls -> text "struct" <+>. textAs name ident <+>. text "{" <+>. structDeclList decls <+> text "}"
  -- anonStruct <- define $ \decls -> text "struct" <+>. text "{" <+>. structDeclList decls <+>. text "}"
  return $ \x ->
    case_
      x
      [ unTVoid $ text "void"
      , unTChar $ text "char"
      , unTShort $ text "short"
      , unTInt $ text "int"
      , unTLong $ text "long"
      , unTFloat $ text "float"
      , unTDouble $ text "double"
      , unTSigned $ text "signed"
      , unTUnsigned $ text "unsigned"
      , -- , unTStruct $ \n decls -> struct n decls
        -- , unTAnonStruct $ \decls -> anonStruct decls
        unTName $ \n -> textAs n ident
      ]

-- pprParamList :: (FliPprD a e) => FliPprM e (A a ParamList -> E e D)
pprParamList :: FliPprM Explicit v (In v ParamList -> F.Exp Explicit v D)
pprParamList = do
  pDecl <- pprDecl
  pAbsDecl <- pprAbstractDecl
  pSpecList <- pprDeclSpecifier >>= list
  pParameter <- define $ \x ->
    case_
      x
      [ unPDecl $ \ds d -> pSpecList ds <> pDecl d
      , unPAbsDecl $ \ds d -> pSpecList ds <> pAbsDecl d
      , unPSpecOnly $ \ds -> pSpecList ds
      ]
  pParameterList <- sepBy "," pParameter
  return $ \x ->
    case_
      x
      [ unVariadic $ \ps -> pParameterList ps <> text "," <+> text "..."
      , unFixed $ \ps -> pParameterList ps
      ]

keywords :: [String]
keywords = ["void", "char", "short", "int", "long", "float", "double", "signed", "unsigned", "const", "volatile", "auto", "register", "static", "extern", "typedef"]

ident :: AM.DFA Char
ident =
  ( AM.unions [AM.range 'a' 'z', AM.range 'A' 'Z', AM.singleton '_']
      <> AM.star (AM.unions [AM.range 'a' 'z', AM.range 'A' 'Z', digit, AM.singleton '_'])
  )
    `AM.difference` AM.unions (map fromString keywords)

-- pprExp :: (FliPprD a e) => FliPprM e (A a Exp -> E e D)
pprExp :: (Phased s) => FliPprM s v (In v Exp -> F.Exp s v D)
pprExp = do
  lit <- pprLit
  identExp <- define $ \x -> textAs x ident
  rec pExp <- define $ \l ->
        case_
          l
          [ unLitExp lit
          , unIdentExp identExp
          , unFunctionCall $ \f args ->
              identExp f
                <#> parens (pExpList args)
          ]
      pExpList <- list pExp
  return pExp

exp1 :: Exp
exp1 = FunctionCall "f" [LitExp $ IntL $ Int 42, LitExp $ FloatL $ Float 3.14, FunctionCall "g" []]

parseAbstractDecl :: [Char] -> Err ann [AbsDecl]
parseAbstractDecl = E.parse $ parsingMode (flippr $ fromFunction <$> pprAbstractDecl)

parseDecl :: [Char] -> Err ann [Decl]
parseDecl = E.parse $ parsingMode (flippr $ fromFunction <$> pprDecl)

main :: IO ()
main =
  defaultMain
    [ bench "abstractDecl" $ whnf (\p -> E.parse (parsingMode p) "*const []") (flippr $ fromFunction <$> pprAbstractDecl)
    , bench "decl" $ whnf (\p -> E.parse (parsingMode p) "*const volatile x[]") (flippr $ fromFunction <$> pprDecl)
    ]
