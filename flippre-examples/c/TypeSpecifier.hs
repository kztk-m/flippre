{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module TypeSpecifier where

import Exp
import Helper
import Literals
import Text.FliPpr
import Types
import Prelude

pprStorageClass :: (FliPprD a e) => FliPprM e (A a StorageClass -> E e D)
pprStorageClass = share $ \x ->
    case_
        x
        [ unSCAuto $ text "auto"
        , unSCRegister $ text "register"
        , unSCStatic $ text "static"
        , unSCExtern $ text "extern"
        , unSCTypedef $ text "typedef"
        ]

pprTypeQualifier :: (FliPprD a e) => FliPprM e (A a TypeQualifier -> E e D)
pprTypeQualifier = share $ \x ->
    case_
        x
        [ unTQConst $ text "const"
        , unTQVolatile $ text "volatile"
        ]

-- todo make prettier
pprPointerList :: (FliPprD a e) => FliPprM e (A a (NonEmpty Pointer) -> E e D)
pprPointerList = do
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
    (FliPprD a e) =>
    (A a Exp -> E e D) ->
    (A a Declarator -> E e D) ->
    (A a [SpecifierQualifier] -> E e D) ->
    FliPprM
        e
        ( A a String -> A a [StructDeclaration] -> E e D
        , A a [StructDeclaration] -> E e D
        , A a String -> A a [StructDeclaration] -> E e D
        , A a [StructDeclaration] -> E e D
        )
pprStruct pCondExp pDeclarator pSpecQualList = do
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
    (FliPprD a e) =>
    (A a (NonEmpty String) -> E e D) ->
    (A a Exp -> E e D) ->
    (A a ParamList -> E e D) ->
    FliPprM
        e
        ( A a Declarator -> E e D
        , A a AbsDeclarator -> E e D
        )
pprDecls pIdentList pCondExp pParamList = do
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
    (FliPprD a e) =>
    (A a Exp -> E e D) ->
    FliPprM
        e
        ( A a String -> A a (NonEmpty Enumerator) -> E e D
        , A a (NonEmpty Enumerator) -> E e D
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
    (FliPprD a e) =>
    (A a Declarator -> E e D) ->
    (A a AbsDeclarator -> E e D) ->
    (A a (NonEmpty DeclarationSpecifier) -> E e D) ->
    FliPprM e (A a ParamList -> E e D)
pprParamList pDeclarator pAbsDeclarator pDeclaratorSpecifierListNonEmpty = do
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
    (FliPprD a e) =>
    (A a Exp -> E e D) ->
    FliPprM
        e
        ( A a TypeName -> E e D
        , A a Declarator -> E e D
        , A a [DeclarationSpecifier] -> E e D
        , A a (NonEmpty DeclarationSpecifier) -> E e D
        )
pprTypes pCondExp = do
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
