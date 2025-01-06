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
    = AbsArray Exp
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
    | DArray DirectDecl Exp
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

data Exp
    = Comma Exp Exp
    | -- assignmentexp
      Assign AssignmentOp Exp Exp
    | -- condexp
      Ternary Exp Exp Exp
    | -- or
      LogicalOrExpOr Exp Exp
    | -- and
      LogicalAndExpAnd Exp Exp
    | -- inclusive or
      InclusiveOrExpOr Exp Exp
    | -- exclusive or
      ExclusiveOrExpXor Exp Exp
    | -- and
      AndExpAnd Exp Exp
    | -- equality
      EqualityExpEq Exp Exp
    | EqualityExpNeq Exp Exp
    | -- relational
      RelationalExpLt Exp Exp
    | RelationalExpGt Exp Exp
    | RelationalExpLe Exp Exp
    | RelationalExpGe Exp Exp
    | -- shift
      ShiftExpLeft Exp Exp
    | ShiftExpRight Exp Exp
    | -- additive
      AdditiveExpPlus Exp Exp
    | AdditiveExpMinus Exp Exp
    | -- multiplicative
      MultiplicativeExpMul Exp Exp
    | MultiplicativeExpDiv Exp Exp
    | MultiplicativeExpMod Exp Exp
    | -- cast
      Cast TypeName Exp
    | -- unary
      Inc Exp
    | Dec Exp
    | UnaryOp UnaryOp Exp
    | SizeofExp Exp
    | SizeofType
        TypeName
    | -- postfix
      PostfixExpCall Exp [Exp]
    | PostfixExpArray Exp Exp
    | PostfixExpDot Exp String
    | PostfixExpArrow Exp String
    | PostfixExpInc Exp
    | PostfixExpDec Exp
    | -- primary exp
      LitExp Literal
    | IdentExp String
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

data UnaryOp
    = Address
    | Indirection
    | Plus
    | Minus
    | BitwiseNot
    | LogicalNot
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
$(mkUn ''AssignmentOp)
$(mkUn ''UnaryOp)
