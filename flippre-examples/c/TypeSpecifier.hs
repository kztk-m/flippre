{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecursiveDo #-}

module TypeSpecifier where

import Helper
import Text.FliPpr hiding (Exp)
import qualified Text.FliPpr as F
import qualified Text.FliPpr.QDo as F
import Types
import Prelude

pprStorageClass :: (Phased s) => FliPprM s v (In v StorageClass -> F.Exp s v D)
pprStorageClass = share $ \x ->
  case_
    x
    [ unSCAuto $ text "auto"
    , unSCRegister $ text "register"
    , unSCStatic $ text "static"
    , unSCExtern $ text "extern"
    , unSCTypedef $ text "typedef"
    ]

pprTypeQualifier :: (Phased s) => FliPprM s v (In v TypeQualifier -> F.Exp s v D)
pprTypeQualifier = share $ \x ->
  case_
    x
    [ unTQConst $ text "const"
    , unTQVolatile $ text "volatile"
    ]

-- todo make prettier
pprPointerList :: (Phased s) => FliPprM s v (In v (NonEmpty Pointer) -> F.Exp s v D)
pprPointerList = F.do
  pTypeQualifier <- pprTypeQualifier
  typeQualifierList <- inlineList pTypeQualifier
  pointer <- share $ \p ->
    case_
      p
      [ unPointer $ \qs ->
          text "*"
            <> typeQualifierList qs
      ]
  rec pointerList <- sepByNonEmpty (text "") pointer
  return pointerList

pprStruct ::
  (Phased s) =>
  (In v Exp -> F.Exp s v D)
  -> (In v Declarator -> F.Exp s v D)
  -> (In v [SpecifierQualifier] -> F.Exp s v D)
  -> FliPprM
      s
      v
      ( In v [Char] -> In v [StructDeclaration] -> F.Exp s v D
      , In v [StructDeclaration] -> F.Exp s v D
      , In v [Char] -> In v [StructDeclaration] -> F.Exp s v D
      , In v [StructDeclaration] -> F.Exp s v D
      )
pprStruct pCondExp pDeclarator pSpecQualList = F.do
  rec pStructDeclarator <- share $ \x ->
        case_
          x
          [ unSDDeclarator $ \d -> pDeclarator d
          , unSDBits $ \d e -> pDeclarator d <+> text ":" <+> pCondExp e
          , unSDAnonBits $ \e -> text ":" <+> pCondExp e
          ]
      pStructDeclaratorList <- sepByNonEmpty (text "," <+>. text "") pStructDeclarator
      pStructDeclaration <- share $
        \t -> case_ t [unStructDeclaration $ \s d -> pSpecQualList s <+> pStructDeclaratorList d <> text ";"]
      pStructDeclarationList <- list pStructDeclaration
      pInner <- share $ \decls ->
        text "{"
          <> nest 4 (line <> pStructDeclarationList decls)
          <> line
          <> text "}"
      pStruct <- share $
        \name decls ->
          text "struct"
            <+> textAs name ident
            <+>. pInner decls
      pAnonStruct <- share $
        \decls ->
          text "struct"
            <+>. pInner decls
      pUnion <- share $
        \name decls ->
          text "union"
            <+> textAs name ident
            <+>. pInner decls
      pAnonUnion <- share $
        \decls ->
          text "union"
            <+>. pInner decls
  return (pStruct, pAnonStruct, pUnion, pAnonUnion)

pprDecls ::
  (Phased s) =>
  (In v (NonEmpty String) -> F.Exp s v D)
  -> (In v Exp -> F.Exp s v D)
  -> (In v ParamList -> F.Exp s v D)
  -> FliPprM
      s
      v
      ( In v Declarator -> F.Exp s v D
      , In v AbsDeclarator -> F.Exp s v D
      )
pprDecls pIdentList pCondExp pParamList = F.do
  pointerList <- pprPointerList
  rec pDirectDeclarator <- share $ \x ->
        case_
          x
          [ unDDIdent $ \i -> textAs i ident
          , unDDArray $ \d e -> pDirectDeclarator d <> text "[" <> pCondExp e <> text "]"
          , unDDFunction $ \d -> pDirectDeclarator d <> parens (text "")
          , unDDIdents $ \d args -> pDirectDeclarator d <> parens (pIdentList args)
          , unDDArrayUnsized $ \d -> pDirectDeclarator d <> text "[" <> text "]"
          , unDDDecl $ \d -> parens $ pDeclarator d
          , unDDProto $ \d ps -> pDirectDeclarator d <> parens (pParamList ps)
          ]
      pDeclarator <- share $ \x ->
        case_
          x
          [ unDDirect pDirectDeclarator
          , unDPointer $ \ps d -> pointerList ps <> pDirectDeclarator d
          ]

      -- abstract declarations
      pAbsDirectDeclarator <- share $ \x ->
        case_
          x
          [ unAbsDArray $ \e -> text "[" <> pCondExp e <> text "]"
          , unAbsDFunction $ parens $ text ""
          , unAbsDArrayUnsized $ text "[" <> text "]"
          , unAbsDDecl $ \d -> parens $ pAbsDeclarator d
          , unAbsDProto $ \ps -> parens $ pParamList ps
          ]
      pAbsDeclarator <- share $ \x ->
        case_
          x
          [ unAbsDirect $ \ds -> pAbsDirectDeclarator ds
          , unAbsPointerDecl $ \ps ds -> pointerList ps <> pAbsDirectDeclarator ds
          , unAbsPointer $ \ps -> pointerList ps
          ]
  return (pDeclarator, pAbsDeclarator)

pprEnumerator ::
  (Phased s) =>
  (In v Exp -> F.Exp s v D)
  -> FliPprM
      s
      v
      ( In v [Char] -> In v (NonEmpty Enumerator) -> F.Exp s v D
      , In v (NonEmpty Enumerator) -> F.Exp s v D
      )
pprEnumerator pCondExp = do
  pEnumerator <- share $ \x ->
    case_
      x
      [ unEName $ \n -> textAs n ident
      , unEWithValue $ \n e -> textAs n ident <+> text "=" <+> pCondExp e
      ]
  -- enumerators can only be nonempty
  pEnumeratorList <- sepByNonEmpty (text "," <> line) pEnumerator
  pEnum <- share $ \name enums -> text "enum" <+>. textAs name ident <+>. text "{" <> nest 4 (line <> pEnumeratorList enums) <> line <> text "}"
  pAnonEnum <- share $ \enums -> text "enum" <+>. text "{" <> nest 4 (line <> pEnumeratorList enums) <> line <> text "}"
  return (pEnum, pAnonEnum)

pprParamList ::
  (Phased s) =>
  (In v Declarator -> F.Exp s v D)
  -> (In v AbsDeclarator -> F.Exp s v D)
  -> (In v (NonEmpty DeclarationSpecifier) -> F.Exp s v D)
  -> FliPprM s v (In v ParamList -> F.Exp s v D)
pprParamList pDeclarator pAbsDeclarator pDeclaratorSpecifierListNonEmpty = F.do
  rec pParam <- share $ \x ->
        case_
          x
          [ unPDeclarator $ \ds d -> pDeclaratorSpecifierListNonEmpty ds <+> pDeclarator d
          , unPAbsDeclarator $ \ds d -> pDeclaratorSpecifierListNonEmpty ds <+> pAbsDeclarator d
          , unPSpecifierOnly $ \ds -> pDeclaratorSpecifierListNonEmpty ds -- (makes the parser ambiguous)
          ]
      pInnerList <- sepByNonEmpty (text "," <+>. text "") pParam
      pParamList <- share $ \x ->
        case_
          x
          [ unPLVariadic $ \ps -> pInnerList ps <> text "," <+>. text "..."
          , unPLFixed $ \ps -> pInnerList ps
          ]
  return pParamList

-- BIG TODO: *x doesn't parse (generally: non-tokenized parsing needs some more work)
pprTypes ::
  (Phased s) =>
  (In v Exp -> F.Exp s v D)
  -> FliPprM
      s
      v
      ( In v TypeName -> F.Exp s v D
      , In v Declarator -> F.Exp s v D
      , In v [DeclarationSpecifier] -> F.Exp s v D
      , In v (NonEmpty DeclarationSpecifier) -> F.Exp s v D
      )
pprTypes pCondExp = F.do
  -- seperate out anything that is not recursive
  pTypeQualifier <- pprTypeQualifier
  pStorageClass <- pprStorageClass
  (pEnum, pAnonEnum) <- pprEnumerator pCondExp
  pIdentList <- sepByNonEmpty (text "," <> space) (`textAs` ident)

  -- declarations for parameters
  rec (pStruct, pAnonStruct, pUnion, pAnonUnion) <- pprStruct pCondExp pDeclarator pSpecQualList
      (pDeclarator, pAbsDeclarator) <- pprDecls pIdentList pCondExp pParamList
      pParamList <- pprParamList pDeclarator pAbsDeclarator pDeclarationSpecifierListNonEmpty
      pDeclarationSpecifier <- share $ \x ->
        case_
          x
          [ unDSStor pStorageClass
          , unDSSpec pTypeSpec
          , unDSQual pTypeQualifier
          ]
      pDeclarationSpecifierSpace <- share $ \x -> pDeclarationSpecifier x <> space
      pDeclarationSpecifierList <- sepBy (text "") pDeclarationSpecifierSpace
      pDeclarationSpecifierListNonEmpty <- sepByNonEmpty space pDeclarationSpecifier
      pSpecQual <- share $ \x ->
        case_
          x
          [ unSQSpec pTypeSpec
          , unSQQual pTypeQualifier
          ]
      pSpecQualList <- inlineList pSpecQual

      pTypeSpec <- share $ \x ->
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
      pTypeName <- share $ \x ->
        case_
          x
          [ unTNSpecifierQualifier $ \t -> pSpecQualList t
          , unTNSpecifierQualifierDeclarator $ \t d -> pSpecQualList t <+> pAbsDeclarator d
          ]
  return (pTypeName, pDeclarator, pDeclarationSpecifierList, pDeclarationSpecifierListNonEmpty)
