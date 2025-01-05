{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module TypeSpecifier (
    pprTypes,
) where

import Exp
import Helper
import Literals
import Text.FliPpr
import Types
import Prelude

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

-- todo make prettier
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
    identList <- sepByNonEmpty (text "," <> space) (`textAs` ident)
    pointerList <- pprPointerList
    pEnumerator <- define $ \x ->
        case_
            x
            [ unEnumeratorName $ \n -> textAs n ident
            , unEnumeratorWithValue $ \n e -> textAs n ident <+> text "=" <+> pCondExp e
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
        pDeclSpecList <- sepBy space pDeclSpec
        pDeclSpecListNonEmpty <- sepByNonEmpty space pDeclSpec
        pSpecQual <- define $ \x ->
            case_
                x
                [ unSpec pTypeSpec
                , unQual pTypeQualifier
                ]
        pSpecQualList <- inlineList pSpecQual
        pParameter <- define $ \x ->
            case_
                x
                [ unPDecl $ \ds d -> pDeclSpecListNonEmpty ds <+> pDecl d
                , unPAbsDecl $ \ds d -> pDeclSpecListNonEmpty ds <+> pAbsDecl d
                -- , unPSpecOnly $ \ds -> pDeclSpecListNonEmpty ds -- (makes the parser ambiguous)
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
                , unSBits $ \d e -> pDecl d <+> text ":" <+> pCondExp e
                , unSAnonBits $ \e -> text ":" <+> pCondExp e
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
                    <> nest 1 (line <> pStructDeclarationList decls)
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
                , unDArray $ \d e -> pDirectDecl d <> text "[" <> pCondExp e <> text "]"
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
                [ unAbsArray $ \e -> text "[" <> pCondExp e <> text "]"
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
        pTypeName <- define $ \x ->
            case_
                x
                [ unTSpecQualifier $ \t -> pSpecQualList t
                , unTSpecQualifierDecl $ \t d -> pSpecQualList t <+> pAbsDecl d
                ]
    return (pTypeName, pDecl, pDeclSpecList, pDeclSpecListNonEmpty)
