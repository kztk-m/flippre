{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

import Data.String (fromString)
import Helper
import Literals
import Prettyprinter (Doc)
import Text.FliPpr
import qualified Text.FliPpr.Automaton as AM
import Text.FliPpr.Grammar.Driver.Earley as E
import Prelude

data Exp = LitExp Literal | IdentExp String | FunctionCall String [Exp]
  deriving (Show, Eq)
$(mkUn ''Exp)

data StorageClass = Auto | Register | Static | Extern | Typedef
  deriving (Show, Eq)

$(mkUn ''StorageClass)

pprStorageClass :: (FliPprD a e) => FliPprM e (A a StorageClass -> E e D)
pprStorageClass = define $ \x ->
  case_
    x
    [ unAuto $ text "auto"
    , unRegister $ text "register"
    , unStatic $ text "static"
    , unExtern $ text "extern"
    , unTypedef $ text "typedef"
    ]

data TypeQualifier = TConst | TVolatile
  deriving (Show, Eq)

$(mkUn ''TypeQualifier)

data Decl
  = DPointer [Pointer] DirectDecl
  | DirectDecl DirectDecl
  deriving (Show, Eq)

data ParamList = Variadic [Parameter] | Fixed [Parameter]
  deriving (Show, Eq)

data AbsDirect
  = AbsArray Exp
  | AbsArrayUnsized
  | AbsFunction
  | AbsDecl AbsDecl
  | AbsProto ParamList
  deriving
    ( Show
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
  | DProto DirectDecl ParamList
  deriving
    ( Show
    , Eq
    )

data Pointer = Pointer [TypeQualifier]
  deriving (Show, Eq)

data SpecQualifier = Spec TypeSpecifier | Qual TypeQualifier
  deriving (Show, Eq)

data DeclSpecifier = DeclStor StorageClass | DeclSpec TypeSpecifier | DeclQual TypeQualifier
  deriving (Show, Eq)

type AnyDecl = Either Decl AbsDecl

data StructDeclaration = StructDecl [SpecQualifier] [StructDeclarator]
  deriving (Show, Eq)

data StructDeclarator = SDecl Decl | SBits Decl Exp | SAnonBits Exp
  deriving (Show, Eq)

data Enumerator = EnumeratorName String | EnumeratorWithValue String Exp
  deriving (Show, Eq)

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
  | TStruct String [StructDeclaration]
  | TAnonStruct
      [StructDeclaration]
  | TUnion String [StructDeclaration]
  | TAnonUnion
      [StructDeclaration]
  | TEnum String [Enumerator]
  | TAnonEnum
      [Enumerator]
  | TName
      String
  deriving (Show, Eq)

-- todo ENUM

$(mkUn ''TypeSpecifier)

$(mkUn ''StructDeclaration)
$(mkUn ''StructDeclarator)

$(mkUn ''Decl)
$(mkUn ''DirectDecl)
$(mkUn ''Pointer)
$(mkUn ''DeclSpecifier)
$(mkUn ''AbsDecl)
$(mkUn ''AbsDirect)
$(mkUn ''Parameter)
$(mkUn ''ParamList)
$(mkUn ''SpecQualifier)
$(mkUn ''Enumerator)

pprTypeQualifier :: (FliPprD a e) => FliPprM e (A a TypeQualifier -> E e D)
pprTypeQualifier = define $ \x ->
  case_
    x
    [ unTConst $ text "const"
    , unTVolatile $ text "volatile"
    ]

pprPointerList :: (FliPprD a e) => FliPprM e (A a [Pointer] -> E e D)
pprPointerList = do
  pTypeQualifier <- pprTypeQualifier
  typeQualifierList <- inlineList pTypeQualifier
  pointer <- define $ \p ->
    case_
      p
      [ unPointer $ \qs ->
          text "*"
            <> typeQualifierList qs
      ]
  rec pointerList <- sepBy (text "") pointer
  return pointerList

-- helpPrint = putStrLn . unlines . map (show . pprProgram')

expDecl :: Decl
expDecl = DPointer [Pointer [TConst, TVolatile]] $ DArrayUnsized $ DIdent "x"

-- BIG TODO: *x doesn't parse (generally: non-tokenized parsing needs some more work)
pprTypeSpec :: (FliPprD a e) => FliPprM e (A a TypeSpecifier -> E e D)
pprTypeSpec = do
  pExp <- pprExp
  pTypeQualifier <- pprTypeQualifier
  pStorageClass <- pprStorageClass
  identList <- sepBy (text "," <> space) (`textAs` ident)
  pointerList <- pprPointerList
  pEnumerator <- define $ \x ->
    case_
      x
      [ unEnumeratorName $ \n -> textAs n ident
      , unEnumeratorWithValue $ \n e -> textAs n ident <+> text "=" <+> pExp e
      ]
  pEnumeratorList <- sepBy (text "," <> line) pEnumerator
  pEnum <- define $ \name enums -> text "enum" <+>. textAs name ident <+>. text "{" <+>. nest 1 (pEnumeratorList enums) <> line <> text "}"
  pAnonEnum <- define $ \enums -> text "enum" <+>. text "{" <+>. nest 1 (pEnumeratorList enums) <> line <> text "}"
  rec pSpec <- define $ \x ->
        case_
          x
          [ unDeclStor pStorageClass
          , unDeclSpec pTypeSpec
          , unDeclQual pTypeQualifier
          ]
      pSpecList <- sepBy (text "") $ pSpec
      specQual <- define $ \x ->
        case_
          x
          [ unSpec $ pTypeSpec
          , unQual $ pTypeQualifier
          ]
      specQualList <- inlineList specQual
      structDeclarator <- define $ \x ->
        case_
          x
          [ unSDecl $ \d -> pDecl d
          , unSBits $ \d e -> pDecl d <> text ":" <> pExp e
          , unSAnonBits $ \e -> text ":" <> pExp e
          ]
      structDeclaratorList <- list structDeclarator
      structDeclaration <- define $ \t -> case_ t [unStructDecl $ \s d -> specQualList s <+> structDeclaratorList d <> text ";"]
      structDeclarationList <- list structDeclaration
      struct <- define $ \name decls -> text "struct" <+> textAs name ident <+>. text "{" <> nest 1 (line <> (structDeclarationList decls)) <> line <> text "}"
      anonStruct <- define $ \decls -> text "struct" <+>. text "{" <> nest 1 (line <> structDeclarationList decls) <> line <> text "}"
      union <- define $ \name decls -> text "union" <+> textAs name ident <+>. text "{" <> nest 1 (line <> structDeclarationList decls) <> line <> text "}"
      anonUnion <- define $ \decls -> text "union" <+>. text "{" <> nest 1 (line <> structDeclarationList decls) <> line <> text "}"
      pDirectDecl <- define $ \x ->
        case_
          x
          [ unDIdent $ \i -> textAs i ident
          , unDArray $ \d e -> pDirectDecl d <> text "[" <> pExp e <> text "]"
          , unDFunction $ \d args -> pDirectDecl d <> text "(" <> identList args <> text ")"
          , unDArrayUnsized $ \d -> pDirectDecl d <> text "[" <> text "]"
          , unDDecl $ \d -> parens $ pDecl d
          , unDProto $ \d ps -> pDirectDecl d <> parens (pParamList ps)
          ]
      pDecl <- define $ \x ->
        case_
          x
          [ unDirectDecl pDirectDecl
          , unDPointer $ \ps d -> pointerList ps <+> pDirectDecl d
          ]
      pAbsDirectDecl <- define $ \x ->
        case_
          x
          [ unAbsArray $ \e -> text "[" <> pExp e <> text "]"
          , unAbsFunction $ parens $ text ""
          , unAbsArrayUnsized $ text "[" <> text "]"
          , unAbsDecl $ \d -> parens $ pAbsDecl d
          , unAbsProto $ \ps -> parens $ pParamList ps
          ]
      pAbsDirectDeclList <- sepBy (text "") pAbsDirectDecl
      pAbsDecl <- define $ \x ->
        case_
          x
          [ unAbsDirectDecl $ \ds -> pAbsDirectDeclList ds
          , unAbsPointerDecl $ \ps ds -> pointerList ps <> pAbsDirectDeclList ds
          , unAbsPointer $ \ps -> pointerList ps
          ]
      pParameter <- define $ \x ->
        case_
          x
          [ unPDecl $ \ds d -> pSpecList ds <+> pDecl d
          , unPAbsDecl $ \ds d -> pSpecList ds <+> pAbsDecl d
          , unPSpecOnly $ \ds -> pSpecList ds
          ]
      pParameterList <- sepBy (text "," <> space) pParameter
      pParamList <- define $ \x ->
        case_
          x
          [ unVariadic $ \ps -> pParameterList ps <> text "," <+> text "..."
          , unFixed $ \ps -> pParameterList ps
          ]
      pTypeSpec <- define $ \x ->
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
          , unTStruct $ \n decls ->
              struct
                n
                decls
          , unTAnonStruct $ \decls ->
              anonStruct
                decls
          , unTUnion $ \n decls ->
              union
                n
                decls
          , unTAnonUnion $ \decls ->
              anonUnion
                decls
          , unTEnum $ \n enums ->
              pEnum
                n
                enums
          , unTAnonEnum $ \enums ->
              pAnonEnum
                enums
          , unTName $
              \n -> textAs n ident
          ]
  return pTypeSpec

decl :: TypeSpecifier
decl = TStruct "complex" [StructDecl [Spec (TAnonStruct [StructDecl [Spec (TAnonEnum [EnumeratorName "A", EnumeratorName "B", EnumeratorWithValue "C" (LitExp (IntL (Int 4)))])] [SDecl (DirectDecl (DIdent "xyz"))], StructDecl [Qual TConst, Spec TInt] [SDecl (DPointer [Pointer [], Pointer []] (DIdent "x"))]])] [SDecl (DirectDecl (DIdent "nestedStruct"))], StructDecl [Qual TConst, Qual TVolatile, Spec TInt] [SDecl (DPointer [Pointer []] (DIdent "x"))]]

keywords :: [String]
keywords = ["void", "char", "short", "int", "long", "float", "double", "signed", "unsigned", "const", "volatile", "auto", "register", "static", "extern", "typedef"]

ident :: AM.DFA Char
ident =
  ( AM.unions [AM.range 'a' 'z', AM.range 'A' 'Z', AM.singleton '_']
      <> AM.star (AM.unions [AM.range 'a' 'z', AM.range 'A' 'Z', digit, AM.singleton '_'])
  )
    `AM.difference` AM.unions (map fromString keywords)

pprExp :: (FliPprD a e) => FliPprM e (A a Exp -> E e D)
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
      pExpList <- inlineList pExp
  return pExp

pprProgram :: TypeSpecifier -> Doc ann
pprProgram = pprMode (flippr $ fromFunction <$> pprTypeSpec)

parseProgram :: [Char] -> Err ann [TypeSpecifier]
parseProgram = E.parse $ parsingMode (flippr $ fromFunction <$> pprTypeSpec)
