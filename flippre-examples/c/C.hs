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

data StorageClass = Auto | Register | Static | Extern | Typedef
  deriving (Show, Eq)

data TypeQualifier = TConst | TVolatile
  deriving (Show, Eq)

data Decl
  = DPointer (NonEmpty Pointer) DirectDecl
  | DirectDecl DirectDecl
  deriving (Show, Eq)

data ParamList = Variadic (NonEmpty Parameter) | Fixed (NonEmpty Parameter)
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

data AbsDecl = AbsPointer (NonEmpty Pointer) | AbsPointerDecl (NonEmpty Pointer) AbsDirect | AbsDirectDecl AbsDirect
  deriving (Show, Eq)

data Parameter = PDecl [DeclSpecifier] Decl | PAbsDecl [DeclSpecifier] AbsDecl | PSpecOnly (NonEmpty DeclSpecifier)
  deriving (Show, Eq)

data DirectDecl
  = DIdent String
  | DArray DirectDecl Exp
  | DArrayUnsized DirectDecl
  | DIdents DirectDecl (NonEmpty String)
  | DFunction DirectDecl
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

data StructDeclaration = StructDecl [SpecQualifier] (NonEmpty StructDeclarator)
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
  | TEnum String (NonEmpty Enumerator)
  | TAnonEnum
      (NonEmpty Enumerator)
  | TName
      String
  deriving (Show, Eq)

$(mkUn ''Exp)
$(mkUn ''StorageClass)
$(mkUn ''TypeQualifier)
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

pprTypeQualifier :: (FliPprD a e) => FliPprM e (A a TypeQualifier -> E e D)
pprTypeQualifier = define $ \x ->
  case_
    x
    [ unTConst $ text "const"
    , unTVolatile $ text "volatile"
    ]

-- todo
pprPointerList :: (FliPprD a e) => FliPprM e (A a (NonEmpty Pointer) -> E e D)
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
  rec pointerList <- sepByNonEmpty (text "") pointer
  return pointerList

-- helpPrint = putStrLn . unlines . map (show . pprProgram')

-- BIG TODO: *x doesn't parse (generally: non-tokenized parsing needs some more work)
pprTypeSpec :: (FliPprD a e) => FliPprM e (A a Exp -> E e D) -> FliPprM e (A a TypeSpecifier -> E e D)
pprTypeSpec pprExp = do
  -- for later knot-tying
  pExp <- pprExp
  -- seperate out anything that is not recursive
  pTypeQualifier <- pprTypeQualifier
  pStorageClass <- pprStorageClass
  identList <- sepByNonEmpty (text "," <> space) (`textAs` ident)
  pointerList <- pprPointerList
  pEnumerator <- define $ \x ->
    case_
      x
      [ unEnumeratorName $ \n -> textAs n ident
      , unEnumeratorWithValue $ \n e -> textAs n ident <+> text "=" <+> pExp e
      ]
  -- enumerators can only be nonempty
  pEnumeratorList <- sepByNonEmpty (text "," <> line) pEnumerator
  pEnum <- define $ \name enums -> text "enum" <+>. textAs name ident <+>. text "{" <> nest 1 (line <> pEnumeratorList enums) <> line <> text "}"
  pAnonEnum <- define $ \enums -> text "enum" <+>. text "{" <> nest 1 (line <> pEnumeratorList enums) <> line <> text "}"

  -- declarations for parameters
  rec pDeclSpec <- define $ \x ->
        case_
          x
          [ unDeclStor pStorageClass
          , unDeclSpec pTypeSpec
          , unDeclQual pTypeQualifier
          ]
      pDeclSpecList <- sepBy (text "") $ pDeclSpec
      pDeclSpecListNonEmpty <- sepByNonEmpty (text "") $ pDeclSpec
      pSpecQual <- define $ \x ->
        case_
          x
          [ unSpec $ pTypeSpec
          , unQual $ pTypeQualifier
          ]
      pSpecQualList <- inlineList pSpecQual
      pParameter <- define $ \x ->
        case_
          x
          [ unPDecl $ \ds d -> pDeclSpecList ds <+> pDecl d
          , unPAbsDecl $ \ds d -> pDeclSpecList ds <+> pAbsDecl d
          , unPSpecOnly $ \ds -> pDeclSpecListNonEmpty ds
          ]
      pParameterList <- sepByNonEmpty (text "," <> space) pParameter
      pParamList <- define $ \x ->
        case_
          x
          [ unVariadic $ \ps -> pParameterList ps <> text "," <+> text "..."
          , unFixed $ \ps -> pParameterList ps
          ]

      -- struct stuff
      pStructDeclarator <- define $ \x ->
        case_
          x
          [ unSDecl $ \d -> pDecl d
          , unSBits $ \d e -> pDecl d <+> text ":" <+> pExp e
          , unSAnonBits $ \e -> text ":" <+> pExp e
          ]
      pStructDeclaratorList <- sepByNonEmpty (text "," <> space) pStructDeclarator
      pStructDeclaration <- define $
        \t -> case_ t [unStructDecl $ \s d -> pSpecQualList s <+> pStructDeclaratorList d <> text ";"]
      pStructDeclarationList <- list pStructDeclaration

      pStruct <- define $
        \name decls ->
          text "struct"
            <+> textAs name ident
            <+>. text "{"
            <> nest 1 (line <> (pStructDeclarationList decls))
            <> line
            <> text "}"
      pAnonStruct <- define $
        \decls ->
          text "struct"
            <+>. text "{"
            <> nest 1 (line <> pStructDeclarationList decls)
            <> line
            <> text "}"
      pUnion <- define $
        \name decls ->
          text "union"
            <+> textAs name ident
            <+>. text "{"
            <> nest 1 (line <> pStructDeclarationList decls)
            <> line
            <> text "}"
      pAnonUnion <- define $
        \decls ->
          text "union"
            <+>. text "{"
            <> nest 1 (line <> pStructDeclarationList decls)
            <> line
            <> text "}"

      -- declarations
      pDirectDecl <- define $ \x ->
        case_
          x
          [ unDIdent $ \i -> textAs i ident
          , unDArray $ \d e -> pDirectDecl d <> text "[" <> pExp e <> text "]"
          , unDFunction $ \d -> pDirectDecl d <> parens (text "")
          , unDIdents $ \d args -> pDirectDecl d <> parens (identList args)
          , unDArrayUnsized $ \d -> pDirectDecl d <> text "[" <> text "]"
          , unDDecl $ \d -> parens $ pDecl d
          , unDProto $ \d ps -> pDirectDecl d <> parens (pParamList ps)
          ]
      pDecl <- define $ \x ->
        case_
          x
          [ unDirectDecl pDirectDecl
          , unDPointer $ \ps d -> pointerList ps <> pDirectDecl d
          ]

      -- abstract declarations
      pAbsDirectDecl <- define $ \x ->
        case_
          x
          [ unAbsArray $ \e -> text "[" <> pExp e <> text "]"
          , unAbsFunction $ parens $ text ""
          , unAbsArrayUnsized $ text "[" <> text "]"
          , unAbsDecl $ \d -> parens $ pAbsDecl d
          , unAbsProto $ \ps -> parens $ pParamList ps
          ]
      pAbsDecl <- define $ \x ->
        case_
          x
          [ unAbsDirectDecl $ \ds -> pAbsDirectDecl ds
          , unAbsPointerDecl $ \ps ds -> pointerList ps <> pAbsDirectDecl ds
          , unAbsPointer $ \ps -> pointerList ps
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
              pStruct
                n
                decls
          , unTAnonStruct $ \decls ->
              pAnonStruct
                decls
          , unTUnion $ \n decls ->
              pUnion
                n
                decls
          , unTAnonUnion $ \decls ->
              pAnonUnion
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
  ]

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
pprProgram = pprMode (flippr $ fromFunction <$> (pprTypeSpec pprExp))

parseProgram :: [Char] -> Err ann [TypeSpecifier]
parseProgram = E.parse $ parsingMode (flippr $ fromFunction <$> (pprTypeSpec pprExp))

exmp :: TypeSpecifier
exmp = TStruct "complex" [StructDecl [Spec (TAnonStruct [StructDecl [Spec (TAnonEnum (NCons (EnumeratorName "A") (NCons (EnumeratorName "B") (NNil (EnumeratorWithValue "C" (LitExp (IntL (Int 4))))))))] (NNil (SDecl (DirectDecl (DIdent "xyz")))), StructDecl [Qual TConst, Spec TInt] (NNil (SDecl (DPointer (NCons (Pointer []) (NNil (Pointer []))) (DIdent "x"))))])] (NNil (SBits (DirectDecl (DFunction (DIdent "nestedStruct"))) (LitExp (IntL (Int 3))))), StructDecl [Qual TConst, Qual TVolatile, Spec TInt] (NNil (SDecl (DPointer (NNil (Pointer [])) (DIdent "x"))))]