{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

import Helper
import Literals
import Prettyprinter (Doc)
import Text.FliPpr
import Text.FliPpr.Grammar.Driver.Earley as E
import Prelude

data Exp = Comma Exp AssignmentExp | Assignment AssignmentExp
  deriving (Show, Eq)

data PrimaryExp = LitExp Literal | IdentExp String | Exp Exp
  deriving (Show, Eq)

data AssignmentExp = Assign AssignmentOp UnaryExp AssignmentExp | CondExp CondExp
  deriving (Show, Eq)

data AssignmentOp
  = AssignOp
  | MulAssign
  | DivAssign
  | ModAssign
  | AddAssign
  | SubAssign
  | LeftAssign
  | RightAssign
  | AndAssign
  | XorAssign
  | OrAssign
  deriving (Show, Eq)

data UnaryExp
  = PostfixExp PostfixExp
  | Inc UnaryExp
  | Dec UnaryExp
  | UnaryOp UnaryOp CastExp
  | SizeofExp UnaryExp
  | SizeofType TypeName
  deriving (Show, Eq)

data UnaryOp
  = Address
  | Indirection
  | Plus
  | Minus
  | BitwiseNot
  | LogicalNot
  deriving (Show, Eq)

data CastExp
  = Cast TypeName CastExp
  | Unary UnaryExp
  deriving (Show, Eq)

data CondExp
  = LogicalOrExp LogicalOrExp
  | LogicalOrExpCond LogicalOrExp Exp CondExp
  deriving (Show, Eq)

data LogicalOrExp
  = LogicalAndExp LogicalAndExp
  | LogicalOrExpOr LogicalOrExp LogicalAndExp
  deriving (Show, Eq)

data LogicalAndExp
  = InclusiveOrExp InclusiveOrExp
  | LogicalAndExpAnd LogicalAndExp InclusiveOrExp
  deriving (Show, Eq)

data InclusiveOrExp
  = ExclusiveOrExp ExclusiveOrExp
  | InclusiveOrExpOr InclusiveOrExp ExclusiveOrExp
  deriving (Show, Eq)

data ExclusiveOrExp
  = AndExp AndExp
  | ExclusiveOrExpXor ExclusiveOrExp AndExp
  deriving (Show, Eq)

data AndExp
  = EqualityExp EqualityExp
  | AndExpAnd AndExp EqualityExp
  deriving (Show, Eq)

data EqualityExp
  = RelationalExp RelationalExp
  | EqualityExpEq EqualityExp RelationalExp
  | EqualityExpNeq EqualityExp RelationalExp
  deriving (Show, Eq)

data RelationalExp
  = ShiftExp ShiftExp
  | RelationalExpLt RelationalExp ShiftExp
  | RelationalExpGt RelationalExp ShiftExp
  | RelationalExpLe RelationalExp ShiftExp
  | RelationalExpGe RelationalExp ShiftExp
  deriving (Show, Eq)

data ShiftExp
  = AdditiveExp AdditiveExp
  | ShiftExpLeft ShiftExp AdditiveExp
  | ShiftExpRight ShiftExp AdditiveExp
  deriving (Show, Eq)

data AdditiveExp
  = MultiplicativeExp MultiplicativeExp
  | AdditiveExpPlus AdditiveExp MultiplicativeExp
  | AdditiveExpMinus AdditiveExp MultiplicativeExp
  deriving (Show, Eq)

data MultiplicativeExp
  = CastExp CastExp
  | MultiplicativeExpMul MultiplicativeExp CastExp
  | MultiplicativeExpDiv MultiplicativeExp CastExp
  | MultiplicativeExpMod MultiplicativeExp CastExp
  deriving (Show, Eq)

data PostfixExp
  = PrimaryExp PrimaryExp
  | PostfixExpCall PostfixExp [AssignmentExp]
  | PostfixExpArray PostfixExp Exp
  | PostfixExpDot PostfixExp String
  | PostfixExpArrow PostfixExp String
  | PostfixExpInc PostfixExp
  | PostfixExpDec PostfixExp
  deriving (Show, Eq)

data TypeName = TSpecQualifier [SpecQualifier] | TSpecQualifierDecl [SpecQualifier] AbsDecl
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
  = AbsArray CondExp
  | AbsArrayUnsized
  | AbsFunction
  | AbsDecl AbsDecl
  | AbsProto ParamList
  deriving (Show, Eq)

data AbsDecl = AbsPointer (NonEmpty Pointer) | AbsPointerDecl (NonEmpty Pointer) AbsDirect | AbsDirectDecl AbsDirect
  deriving (Show, Eq)

data Parameter = PDecl [DeclSpecifier] Decl | PAbsDecl [DeclSpecifier] AbsDecl | PSpecOnly (NonEmpty DeclSpecifier)
  deriving (Show, Eq)

data DirectDecl
  = DIdent String
  | DArray DirectDecl CondExp
  | DArrayUnsized DirectDecl
  | DIdents DirectDecl (NonEmpty String)
  | DFunction DirectDecl
  | DDecl Decl
  | DProto DirectDecl ParamList
  deriving (Show, Eq)

newtype Pointer = Pointer [TypeQualifier]
  deriving (Show, Eq)

data SpecQualifier = Spec TypeSpecifier | Qual TypeQualifier
  deriving (Show, Eq)

data DeclSpecifier = DeclStor StorageClass | DeclSpec TypeSpecifier | DeclQual TypeQualifier
  deriving (Show, Eq)

data StructDeclaration = StructDecl [SpecQualifier] (NonEmpty StructDeclarator)
  deriving (Show, Eq)

data StructDeclarator = SDecl Decl | SBits Decl CondExp | SAnonBits CondExp
  deriving (Show, Eq)

data Enumerator = EnumeratorName String | EnumeratorWithValue String CondExp
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
$(mkUn ''PrimaryExp)
$(mkUn ''AssignmentExp)
$(mkUn ''AssignmentOp)
$(mkUn ''UnaryExp)
$(mkUn ''UnaryOp)
$(mkUn ''CastExp)
$(mkUn ''CondExp)
$(mkUn ''LogicalOrExp)
$(mkUn ''LogicalAndExp)
$(mkUn ''InclusiveOrExp)
$(mkUn ''ExclusiveOrExp)
$(mkUn ''AndExp)
$(mkUn ''EqualityExp)
$(mkUn ''RelationalExp)
$(mkUn ''ShiftExp)
$(mkUn ''AdditiveExp)
$(mkUn ''MultiplicativeExp)
$(mkUn ''PostfixExp)
$(mkUn ''TypeName)

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
pprTypes :: (FliPprD a e) => (A a CondExp -> E e D) -> FliPprM e (A a TypeSpecifier -> E e D, A a TypeName -> E e D)
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
      pDeclSpecList <- sepBy (text "") pDeclSpec
      pDeclSpecListNonEmpty <- sepByNonEmpty (text "") pDeclSpec
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
  return (pTypeSpec, pTypeName)

pprExp :: (FliPprD a e) => (A a TypeName -> E e D) -> FliPprM e (A a Exp -> E e D, A a CondExp -> E e D)
pprExp pTypeName = do
  lit <- pprLit
  pAssignmentOp <- define $ \x ->
    case_
      x
      [ unAssignOp $ text "="
      , unMulAssign $ text "*="
      , unDivAssign $ text "/="
      , unModAssign $ text "%="
      , unAddAssign $ text "+="
      , unSubAssign $ text "-="
      , unLeftAssign $ text "<<="
      , unRightAssign $ text ">>="
      , unAndAssign $ text "&="
      , unXorAssign $ text "^="
      , unOrAssign $ text "|="
      ]
  identExp <- define $ \x -> textAs x ident
  rec pExp <- define $ \x ->
        case_
          x
          [ unComma $ \e1 e2 -> align $ group $ pExp e1 </>. text "," <+>. pAssignmentExp e2
          , unAssignment $ \e -> pAssignmentExp e
          ]
      pAssignmentExp <- define $ \x ->
        case_
          x
          [ unAssign $ \op e1 e2 -> pUnaryExp e1 <+>. pAssignmentOp op <+>. pAssignmentExp e2
          , unCondExp $ \e -> pCondExp e
          ]
      pCondExp <- define $ \x ->
        case_
          x
          [ unLogicalOrExp $ \e -> pLogicalOrExp e
          , unLogicalOrExpCond $ \e1 e2 e3 -> pLogicalOrExp e1 <+> align (vsep [text "?" <+>. pExp e2, text ":" <+>. pCondExp e3])
          ]
      pLogicalOrExp <- define $ \x ->
        case_
          x
          [ unLogicalAndExp $ \e -> pLogicalAndExp e
          , unLogicalOrExpOr $ \e1 e2 -> align $ group $ pLogicalOrExp e1 </>. text "||" <+>. pLogicalAndExp e2
          ]
      pLogicalAndExp <- define $ \x ->
        case_
          x
          [ unInclusiveOrExp $ \e -> pInclusiveOrExp e
          , unLogicalAndExpAnd $ \e1 e2 -> align $ group $ pLogicalAndExp e1 </>. text "&&" <+>. pInclusiveOrExp e2
          ]
      pInclusiveOrExp <- define $ \x ->
        case_
          x
          [ unExclusiveOrExp $ \e -> pExclusiveOrExp e
          , unInclusiveOrExpOr $ \e1 e2 -> pInclusiveOrExp e1 <+>. text "|" <+>. pExclusiveOrExp e2
          ]
      pExclusiveOrExp <- define $ \x ->
        case_
          x
          [ unAndExp $ \e -> pAndExp e
          , unExclusiveOrExpXor $ \e1 e2 -> pExclusiveOrExp e1 <+>. text "^" <+>. pAndExp e2
          ]
      pAndExp <- define $ \x ->
        case_
          x
          [ unEqualityExp $ \e -> pEqualityExp e
          , unAndExpAnd $ \e1 e2 -> pAndExp e1 <+>. text "&" <+>. pEqualityExp e2
          ]
      pEqualityExp <- define $ \x ->
        case_
          x
          [ unRelationalExp $ \e -> pRelationalExp e
          , unEqualityExpEq $ \e1 e2 -> align $ group $ pEqualityExp e1 </>. text "==" <+>. pRelationalExp e2
          , unEqualityExpNeq $ \e1 e2 -> align $ group $ pEqualityExp e1 </>. text "!=" <+>. pRelationalExp e2
          ]
      pRelationalExp <- define $ \x ->
        case_
          x
          [ unShiftExp $ \e -> pShiftExp e
          , unRelationalExpLt $ \e1 e2 -> align $ group $ pRelationalExp e1 </>. text "<" <+>. pShiftExp e2
          , unRelationalExpGt $ \e1 e2 -> align $ group $ pRelationalExp e1 </>. text ">" <+>. pShiftExp e2
          , unRelationalExpLe $ \e1 e2 -> align $ group $ pRelationalExp e1 </>. text "<=" <+>. pShiftExp e2
          , unRelationalExpGe $ \e1 e2 -> align $ group $ pRelationalExp e1 </>. text ">=" <+>. pShiftExp e2
          ]
      pShiftExp <- define $ \x ->
        case_
          x
          [ unAdditiveExp $ \e -> pAdditiveExp e
          , unShiftExpLeft $ \e1 e2 -> pShiftExp e1 <+>. text "<<" <+>. pAdditiveExp e2
          , unShiftExpRight $ \e1 e2 -> pShiftExp e1 <+>. text ">>" <+>. pAdditiveExp e2
          ]
      pAdditiveExp <- define $ \x ->
        case_
          x
          [ unMultiplicativeExp $ \e -> pMultiplicativeExp e
          , unAdditiveExpPlus $ \e1 e2 -> align $ group $ pAdditiveExp e1 </>. text "+" <+>. pMultiplicativeExp e2
          , unAdditiveExpMinus $ \e1 e2 -> align $ group $ pAdditiveExp e1 </>. text "-" <+>. pMultiplicativeExp e2
          ]
      pMultiplicativeExp <- define $ \x ->
        case_
          x
          [ unCastExp $ \e -> pCastExp e
          , unMultiplicativeExpMul $ \e1 e2 -> pMultiplicativeExp e1 <+>. text "*" <+>. pCastExp e2
          , unMultiplicativeExpDiv $ \e1 e2 -> pMultiplicativeExp e1 <+>. text "/" <+>. pCastExp e2
          , unMultiplicativeExpMod $ \e1 e2 -> pMultiplicativeExp e1 <+>. text "%" <+>. pCastExp e2
          ]
      pAssignmentList <- sepBy (text "," <> space) pAssignmentExp
      pPostfixExp <- define $ \x ->
        case_
          x
          [ unPrimaryExp $ \e -> pPrimaryExp e
          , -- hardcats necessary
            unPostfixExpCall $ \e args -> pPostfixExp e <#> parens (pAssignmentList args)
          , unPostfixExpArray $ \e1 e2 -> pPostfixExp e1 <#> text "[" <> pExp e2 <> text "]"
          , unPostfixExpDot $ \e s -> pPostfixExp e <#> text "." <#> textAs s ident
          , unPostfixExpArrow $ \e s -> pPostfixExp e <#> text "->" <#> textAs s ident
          , unPostfixExpInc $ \e -> pPostfixExp e <#> text "++"
          , unPostfixExpDec $ \e -> pPostfixExp e <#> text "--"
          ]
      pUnaryExp <- define $ \x ->
        case_
          x
          [ unPostfixExp $ \e -> pPostfixExp e
          , unInc $ \e -> text "++" <#> pUnaryExp e
          , unDec $ \e -> text "--" <#> pUnaryExp e
          , unUnaryOp $ \op e -> pUnaryOp op <#> pCastExp e
          , unSizeofExp $ \e -> text "sizeof" <> parens (pUnaryExp e)
          , unSizeofType $ \t -> text "sizeof" <> parens (pTypeName t)
          ]
      pUnaryOp <- define $ \x ->
        case_
          x
          [ unAddress $ text "&"
          , unIndirection $ text "*"
          , unPlus $ text "+"
          , unMinus $ text "-"
          , unBitwiseNot $ text "~"
          , unLogicalNot $ text "!"
          ]
      pCastExp <- define $ \x ->
        case_
          x
          [ unCast $ \t e -> parens (pTypeName t) <+>. pCastExp e
          , unUnary $ \e -> pUnaryExp e
          ]
      pPrimaryExp <-
        define $ \x ->
          case_
            x
            [ unLitExp $ \l -> lit l
            , unIdentExp $ \i -> identExp i
            , unExp $ \e -> parens (pExp e)
            ]

  return (pExp, pCondExp)

pprKnots :: (FliPprD a e) => FliPprM e (A a Exp -> E e D)
pprKnots = do
  rec (pExp, pCondExp) <- pprExp pTypeName
      (_, pTypeName) <- pprTypes pCondExp
  return pExp

pprProgram :: Exp -> Doc ann
pprProgram = pprMode (flippr $ fromFunction <$> pprKnots)

parseProgram :: [Char] -> Err ann [Exp]
parseProgram = E.parse $ parsingMode (flippr $ fromFunction <$> pprKnots)