{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Types where

import Helper
import Literals
import Text.FliPpr
import Prelude

data TypeName = TSpecQualifier [SpecQualifier] | TSpecQualifierDecl [SpecQualifier] AbsDecl
    deriving (Show, Eq)

data StorageClass = Auto | Register | Static | Extern | Typedef
    deriving (Show, Eq)

data TypeQualifier = TConst | TVolatile
    deriving (Show, Eq)

-- TODO Decl->Declarator
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

data Parameter
    = PDecl (NonEmpty DeclSpecifier) Decl
    | PAbsDecl (NonEmpty DeclSpecifier) AbsDecl
    -- \| PSpecOnly (NonEmpty DeclSpecifier)
    -- the existence of PSpecOnly makes the parser ambiguous! and I can't think of any case where it would be useful
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