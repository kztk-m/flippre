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

data TypeName = TNSpecifierQualifier [SpecifierQualifier] | TNSpecifierQualifierDeclarator [SpecifierQualifier] AbsDeclarator
    deriving (Show, Eq)

data StorageClass = SCAuto | SCRegister | SCStatic | SCExtern | SCTypedef
    deriving (Show, Eq)

data TypeQualifier = TQConst | TQVolatile
    deriving (Show, Eq)

data SpecifierQualifier = SQSpec TypeSpecifier | SQQual TypeQualifier
    deriving (Show, Eq)

data DeclarationSpecifier = DSStor StorageClass | DSSpec TypeSpecifier | DSQual TypeQualifier
    deriving (Show, Eq)

newtype Pointer = Pointer [TypeQualifier]
    deriving (Show, Eq)

data Declarator
    = DPointer (NonEmpty Pointer) DirectDeclarator
    | DDirect DirectDeclarator
    deriving (Show, Eq)

data DirectDeclarator
    = DDIdent String
    | DDArray DirectDeclarator Exp
    | DDArrayUnsized DirectDeclarator
    | DDIdents DirectDeclarator (NonEmpty String)
    | DDFunction DirectDeclarator
    | DDDecl Declarator
    | DDProto DirectDeclarator ParamList
    deriving (Show, Eq)

data AbsDeclarator
    = AbsPointer (NonEmpty Pointer)
    | AbsPointerDecl (NonEmpty Pointer) AbsDirectDeclarator
    | AbsDirect AbsDirectDeclarator
    deriving (Show, Eq)

data AbsDirectDeclarator
    = AbsDArray Exp
    | AbsDArrayUnsized
    | AbsDFunction
    | AbsDDecl AbsDeclarator
    | AbsDProto ParamList
    deriving (Show, Eq)

data Param
    = PDeclarator (NonEmpty DeclarationSpecifier) Declarator
    | PAbsDeclarator (NonEmpty DeclarationSpecifier) AbsDeclarator
    -- \| PSpecOnly (NonEmpty DeclarationSpecifier)
    -- the existence of PSpecOnly makes the parser ambiguous! and I can't think of any case where it would be useful
    deriving (Show, Eq)

data ParamList = PLVariadic (NonEmpty Param) | PLFixed (NonEmpty Param)
    deriving (Show, Eq)

data StructDeclaration = StructDeclaration [SpecifierQualifier] (NonEmpty StructDeclarator)
    deriving (Show, Eq)

data StructDeclarator = SDDeclarator Declarator | SDBits Declarator Exp | SDAnonBits Exp
    deriving (Show, Eq)

data Enumerator = EName String | EWithValue String Exp
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
    | -- assignment exp
      Assign AssignmentOp Exp Exp
    | -- cond exp
      Ternary Exp Exp Exp
    | -- logical or exp
      LogicalOr Exp Exp
    | -- logical and exp
      LogicalAnd Exp Exp
    | -- inclusive or
      BitewiseOr Exp Exp
    | -- exclusive or
      BitewiseXor Exp Exp
    | -- and exp
      BitewiseAnd Exp Exp
    | -- equality exp
      Eq Exp Exp
    | Neq Exp Exp
    | -- relational exp
      Lt Exp Exp
    | Gt Exp Exp
    | Le Exp Exp
    | Ge Exp Exp
    | -- shift exp
      ShiftLeft Exp Exp
    | ShiftRight Exp Exp
    | -- additive exp
      Add Exp Exp
    | Sub Exp Exp
    | -- multiplicative exp
      Mul Exp Exp
    | Div Exp Exp
    | Mod Exp Exp
    | -- cast exp
      Cast TypeName Exp
    | -- unary exp
      Inc Exp
    | Dec Exp
    | UnaryOp UnaryOp Exp
    | SizeofExp Exp
    | SizeofType TypeName
    | -- postfix exp
      PostfixCall Exp [Exp]
    | PostfixArrayIndex Exp Exp
    | PostfixDot Exp String
    | PostfixArrow Exp String
    | PostfixInc Exp
    | PostfixDec Exp
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
$(mkUn ''Declarator)
$(mkUn ''DirectDeclarator)
$(mkUn ''Pointer)
$(mkUn ''DeclarationSpecifier)
$(mkUn ''AbsDeclarator)
$(mkUn ''AbsDirectDeclarator)
$(mkUn ''Param)
$(mkUn ''ParamList)
$(mkUn ''SpecifierQualifier)
$(mkUn ''Enumerator)

$(mkUn ''Exp)
$(mkUn ''AssignmentOp)
$(mkUn ''UnaryOp)
