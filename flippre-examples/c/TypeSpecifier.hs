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
        [ unAuto $ text "auto"
        , unRegister $ text "register"
        , unStatic $ text "static"
        , unExtern $ text "extern"
        , unTypedef $ text "typedef"
        ]

pprTypeQualifier :: (FliPprD a e) => FliPprM e (A a TypeQualifier -> E e D)
pprTypeQualifier = share $ \x ->
    case_
        x
        [ unTConst $ text "const"
        , unTVolatile $ text "volatile"
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
    (A a CondExp -> E e D) ->
    (A a Decl -> E e D) ->
    (A a [SpecQualifier] -> E e D) ->
    FliPprM
        e
        ( A a String -> A a [StructDeclaration] -> E e D
        , A a [StructDeclaration] -> E e D
        , A a String -> A a [StructDeclaration] -> E e D
        , A a [StructDeclaration] -> E e D
        )
pprStruct pCondExp pDecl pSpecQualList = do
    rec pStructDeclarator <- share $ \x ->
            case_
                x
                [ unSDecl $ \d -> pDecl d
                , unSBits $ \d e -> pDecl d <+> text ":" <+> pCondExp e
                , unSAnonBits $ \e -> text ":" <+> pCondExp e
                ]
        pStructDeclaratorList <- sepByNonEmpty (text "," <+>. text "") pStructDeclarator
        pStructDeclaration <- share $
            \t -> case_ t [unStructDecl $ \s d -> pSpecQualList s <+> pStructDeclaratorList d <> text ";"]
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
    (A a CondExp -> E e D) ->
    (A a ParamList -> E e D) ->
    FliPprM
        e
        ( A a Decl -> E e D
        , A a AbsDecl -> E e D
        )
pprDecls pIdentList pCondExp pParamList = do
    pointerList <- pprPointerList
    rec pDirectDecl <- share $ \x ->
            case_
                x
                [ unDIdent $ \i -> textAs i ident
                , unDArray $ \d e -> pDirectDecl d <> text "[" <> pCondExp e <> text "]"
                , unDFunction $ \d -> pDirectDecl d <> parens (text "")
                , unDIdents $ \d args -> pDirectDecl d <> parens (pIdentList args)
                , unDArrayUnsized $ \d -> pDirectDecl d <> text "[" <> text "]"
                , unDDecl $ \d -> parens $ pDecl d
                , unDProto $ \d ps -> pDirectDecl d <> parens (pParamList ps)
                ]
        pDecl <- share $ \x ->
            case_
                x
                [ unDirectDecl pDirectDecl
                , unDPointer $ \ps d -> pointerList ps <> pDirectDecl d
                ]

        -- abstract declarations
        pAbsDirectDecl <- share $ \x ->
            case_
                x
                [ unAbsArray $ \e -> text "[" <> pCondExp e <> text "]"
                , unAbsFunction $ parens $ text ""
                , unAbsArrayUnsized $ text "[" <> text "]"
                , unAbsDecl $ \d -> parens $ pAbsDecl d
                , unAbsProto $ \ps -> parens $ pParamList ps
                ]
        pAbsDecl <- share $ \x ->
            case_
                x
                [ unAbsDirectDecl $ \ds -> pAbsDirectDecl ds
                , unAbsPointerDecl $ \ps ds -> pointerList ps <> pAbsDirectDecl ds
                , unAbsPointer $ \ps -> pointerList ps
                ]
    return (pDecl, pAbsDecl)

pprEnumerator ::
    (FliPprD a e) =>
    (A a CondExp -> E e D) ->
    FliPprM
        e
        ( A a String -> A a (NonEmpty Enumerator) -> E e D
        , A a (NonEmpty Enumerator) -> E e D
        )
pprEnumerator pCondExp = do
    pEnumerator <- share $ \x ->
        case_
            x
            [ unEnumeratorName $ \n -> textAs n ident
            , unEnumeratorWithValue $ \n e -> textAs n ident <+> text "=" <+> pCondExp e
            ]
    -- enumerators can only be nonempty
    pEnumeratorList <- sepByNonEmpty (text "," <> line) pEnumerator
    pEnum <- share $ \name enums -> text "enum" <+>. textAs name ident <+>. text "{" <> nest 4 (line <> pEnumeratorList enums) <> line <> text "}"
    pAnonEnum <- share $ \enums -> text "enum" <+>. text "{" <> nest 4 (line <> pEnumeratorList enums) <> line <> text "}"
    return (pEnum, pAnonEnum)

pprParamList ::
    (FliPprD a e) =>
    (A a Decl -> E e D) ->
    (A a AbsDecl -> E e D) ->
    (A a (NonEmpty DeclSpecifier) -> E e D) ->
    FliPprM e (A a ParamList -> E e D)
pprParamList pDecl pAbsDecl pDeclSpecListNonEmpty = do
    rec pParameter <- share $ \x ->
            case_
                x
                [ unPDecl $ \ds d -> pDeclSpecListNonEmpty ds <+> pDecl d
                , unPAbsDecl $ \ds d -> pDeclSpecListNonEmpty ds <+> pAbsDecl d
                -- , unPSpecOnly $ \ds -> pDeclSpecListNonEmpty ds -- (makes the parser ambiguous)
                ]
        pParameterList <- sepByNonEmpty (text "," <> space) pParameter
        pParamList <- share $ \x ->
            case_
                x
                [ unVariadic $ \ps -> pParameterList ps <> text "," <+> text "..."
                , unFixed $ \ps -> pParameterList ps
                ]
    return pParamList

-- BIG TODO: *x doesn't parse (generally: non-tokenized parsing needs some more work)
pprTypes ::
    (FliPprD a e) =>
    (A a CondExp -> E e D) ->
    FliPprM
        e
        ( A a TypeName -> E e D
        , A a Decl -> E e D
        , A a [DeclSpecifier] -> E e D
        , A a (NonEmpty DeclSpecifier) -> E e D
        )
pprTypes pCondExp = do
    -- seperate out anything that is not recursive
    pTypeQualifier <- pprTypeQualifier
    pStorageClass <- pprStorageClass
    (pEnum, pAnonEnum) <- pprEnumerator pCondExp
    pIdentList <- sepByNonEmpty (text "," <> space) (`textAs` ident)

    -- declarations for parameters
    rec (pStruct, pAnonStruct, pUnion, pAnonUnion) <- pprStruct pCondExp pDecl pSpecQualList
        (pDecl, pAbsDecl) <- pprDecls pIdentList pCondExp pParamList
        pParamList <- pprParamList pDecl pAbsDecl pDeclSpecListNonEmpty
        pDeclSpec <- share $ \x ->
            case_
                x
                [ unDeclStor pStorageClass
                , unDeclSpec pTypeSpec
                , unDeclQual pTypeQualifier
                ]
        pDeclSpecList <- sepBy space pDeclSpec
        pDeclSpecListNonEmpty <- sepByNonEmpty space pDeclSpec
        pSpecQual <- share $ \x ->
            case_
                x
                [ unSpec pTypeSpec
                , unQual pTypeQualifier
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
                [ unTSpecQualifier $ \t -> pSpecQualList t
                , unTSpecQualifierDecl $ \t d -> pSpecQualList t <+> pAbsDecl d
                ]
    return (pTypeName, pDecl, pDeclSpecList, pDeclSpecListNonEmpty)
