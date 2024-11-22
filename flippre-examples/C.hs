{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}

-- To suppress warnings caused by TH code.
{-# LANGUAGE MonoLocalBinds            #-}
{-# LANGUAGE RebindableSyntax          #-}


import           Prelude
import           Data.Word (Word64)
import           Numeric (showHex, showOct)
import           Text.FliPpr
import           Text.FliPpr.Grammar.Driver.Earley as E
import qualified Text.FliPpr.Automaton     as AM
import Prettyprinter (Doc)

-- necessary for recursions within do blocks
mfix :: (Arg (E f) a) => (a -> FliPprM f a) -> FliPprM f a
mfix = mfixF


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

data Literal = IntL IntLit | FloatL FloatLit -- TODO missing: Char, String
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




-- type StructDeclList = [(TypeSpecifierQualifier, StructDecl)]

data TypeSpecifier = TVoid | TChar | TShort | TInt | TLong | TFloat | TDouble | TSigned | TUnsigned
                   -- | TStruct String StructDeclList | TAnonStruct StructDeclList -- | TUnion String StructDeclList
                   -- | TEnum String
                   | TName String
                   deriving (Show, Eq)

data TypeQualifier = TConst | TVolatile
                    deriving (Show, Eq)


$(mkUn ''TypeSpecifier)
$(mkUn ''TypeQualifier)

data Decl = DPointer Pointer
          | DirectDecl DirectDecl
          deriving (Show, Eq)

data DirectDecl = DIdent String | DArray DirectDecl Exp | DFunction DirectDecl [String] -- | DProto  more stuff with types here
                deriving (Show, Eq)

data Pointer = Pointer [TypeQualifier] Decl
              deriving (Show, Eq)

$(mkUn ''Decl)
$(mkUn ''DirectDecl)
$(mkUn ''Pointer)

pprTypeQualifier :: FliPprD a e => FliPprM e (A a TypeQualifier -> E e D)
pprTypeQualifier = do
  const <- define $ text "const"
  volatile <- define $ text "volatile"
  return $ \x -> case_ x [ unTConst const
                         , unTVolatile volatile
                         ]


list :: (FliPprD a e, Eq v) => (A a v -> E e D) -> FliPprM e (A a [v] -> E e D)
list p = do 
  rec list' <- define $ \xs -> case_ xs
                           [ unNil $ text ""
                           , unCons $ \t ts -> case_ ts [ unNil $ p t
                                            , unCons $ \_ _ -> p t <+> list' ts
                                            ]
                           ]
  return list'



commaSep :: (FliPprD a e, Eq v) => (A a v -> E e D) -> FliPprM e (A a [v] -> E e D)
commaSep p = do
  rec commaSep' <- define $ \xs -> case_ xs
                           [ unCons $ \t ts -> case_ ts [ unNil $ p t
                                                        , unCons $ \_ _ -> p t <> text "," <+>. commaSep' ts
                                                        ]
                           ]
  return $ \xs -> case_ xs [ unNil $ text ""
                           , unCons $ \_ _ -> commaSep' xs
                           ]

pprDecl :: FliPprD a e => FliPprM e (A a Decl -> E e D)
pprDecl = do
  pExp <- pprExp
  pTypeQualifier <- pprTypeQualifier
  typeQualifierList <- list pTypeQualifier
  identList <- commaSep (`textAs` ident)
  rec pDirectDecl <- define $ \x -> case_ x [ unDIdent $ \i -> textAs i ident
                                            , unDArray $ \d e -> pDirectDecl d <> text "[" <> pExp e <> text "]"
                                            , unDFunction $ \d args -> pDirectDecl d <> text "(" <> identList args <> text ")"
                                            ]
      pointer <- define $ \p ->
                             case_ p [ unPointer $ \qs innerD -> 
                                         case_ qs [
                                             unCons $ \_ _ -> (text "*" <> typeQualifierList qs <+> pDecl innerD)
                                                            <? (typeQualifierList qs <+> pDecl innerD <> text "[]")
                                           , unNil $ (text "*" <> pDecl innerD)
                                                     <? (pDecl innerD <> text "[]")
                                           ]
                                      ]
      pDecl <- define $ \x -> case_ x [ unDirectDecl $ \d -> pDirectDecl d
                                      , unDPointer pointer
                                      ]
  return pDecl

expDecl :: Decl
expDecl = DPointer (Pointer [TConst, TVolatile] (DPointer $ Pointer [TConst] (DirectDecl $ DArray (DIdent "x") (LitExp $ IntL $ Int 42))))

pprTypeSpecQualList :: FliPprD a e => FliPprM e (A a [TypeSpecifier] -> E e D)
pprTypeSpecQualList = do
  void <- define $ text "void"
  char <- define $ text "char"
  short <- define $ text "short"
  int <- define $ text "int"
  long <- define $ text "long"
  float <- define $ text "float"
  double <- define $ text "double"
  signed <- define $ text "signed"
  unsigned <- define $ text "unsigned"
  pExp <- pprExp
  rec pTypeSpecQualList <- define $ \x -> case_ x [ unNil $ text ""
                                                  , unCons $ \t ts -> case_ ts [ unNil $ pType t
                                                                               , unCons $ \_ _ -> pType t <+> pTypeSpecQualList ts]
                                                  ]
      {-structDecl <- define $ \t -> 
      structDeclList <- define $ \x -> case_ x [ unNil $ text ""
                                               , unCons $ \t ts -> case_ ts [ unNil $ structDecl t
                                                                           , unCons $ \_ _ -> structDecl <> line <> structDeclList ts
                                                                           ]
                                               ]-}
      --struct <- define $ \name decls -> text "struct" <+>. textAs name ident <+>. text "{" <+>. structDeclList decls <+> text "}"
      --anonStruct <- define $ \decls -> text "struct" <+>. text "{" <+>. structDeclList decls <+>. text "}"
      pType <- define $ \x -> case_ x [ unTVoid void
                         , unTChar char
                         , unTShort short
                         , unTInt int
                         , unTLong long
                         , unTFloat float
                         , unTDouble double
                         , unTSigned signed
                         , unTUnsigned unsigned
                         --, unTStruct $ \n decls -> struct n decls
                         --, unTAnonStruct $ \decls -> anonStruct decls
                         , unTName $ \n -> textAs n ident
                         ]
  return pTypeSpecQualList



keywords :: [String]
keywords = ["void", "char", "short", "int", "long", "float", "double", "signed", "unsigned", "const", "volatile"]
ident :: AM.DFA Char
ident = (AM.unions [AM.range 'a' 'z', AM.range 'A' 'Z', AM.singleton '_']
      <> AM.star (AM.unions [AM.range 'a' 'z', AM.range 'A' 'Z', digit, AM.singleton '_']))
      `AM.difference`
      AM.unions (map AM.string keywords)


pprExp :: (FliPprD a e) => FliPprM e (A a Exp -> E e D)
pprExp = do
  lit <- pprLit
  identExp <- define $ \x -> textAs x ident
  rec argList <- define $ \a -> case_ a [ unCons $ \x xs -> pExp x <> case_ xs
                                          [ unNil $ text ""
                                          , unCons $ \_ _ -> text "," <+>. argList xs ]
                                        ]
      pExp <- define $ \l -> case_ l [ unLitExp lit
                                     , unIdentExp identExp
                                     , unFunctionCall $ \f args -> identExp f <#> text "("
                                                      <> case_ args [ unNil $ text "" -- TODO: arbitrary whitespace
                                                                    , unCons $ \_ _ -> argList args
                                                                    ] <> text ")"
                                     ]
  return pExp


exp1 :: Exp
exp1 = FunctionCall "f" [LitExp $ IntL $ Int 42, LitExp $ FloatL $ Float 3.14, FunctionCall "g" []]

pprProgram :: Exp -> Doc ann
pprProgram = pprMode (flippr $ fromFunction <$> pprExp)

parseProgram :: [Char] -> Err ann [Exp]
parseProgram = E.parse $ parsingMode (flippr $ fromFunction <$> pprExp)


pprProgram' :: Decl -> Doc ann
pprProgram' = pprMode (flippr $ fromFunction <$> pprDecl)

parseProgram' :: [Char] -> Err ann [Decl]
parseProgram' = E.parse $ parsingMode (flippr $ fromFunction <$> pprDecl)


{-
pprProgram' :: [TypeSpecifierQualifier] -> Doc ann
pprProgram' = pprMode (flippr $ fromFunction <$> pprTypeSpecQualList)


parseProgram' :: [Char] -> Err ann [[TypeSpecifierQualifier]]
parseProgram' = E.parse $ parsingMode (flippr $ fromFunction <$> pprTypeSpecQualList)
-}