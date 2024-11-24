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

-- type StructDeclList = [(TypeSpecifierQualifier, StructDecl)]

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
  | -- | TStruct String StructDeclList | TAnonStruct StructDeclList -- | TUnion String StructDeclList
    -- | TEnum String
    TName String
  deriving (Show, Eq)

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

$(mkUn ''TypeSpecifier)

data TypeQualifier = TConst | TVolatile
  deriving (Show, Eq)

$(mkUn ''TypeQualifier)

data Decl
  = DPointer [Pointer] DirectDecl
  | DirectDecl DirectDecl
  deriving (Show, Eq)

data DirectDecl = DIdent String | DArray DirectDecl Exp | DArrayUnsized DirectDecl | DFunction DirectDecl [String] | DDecl Decl
  -- \| TODO: DProto  more stuff with types here
  deriving
    ( Show
    , Eq
    )

data Pointer = Pointer [TypeQualifier]
  deriving (Show, Eq)

$(mkUn ''Decl)
$(mkUn ''DirectDecl)
$(mkUn ''Pointer)

pprTypeQualifier :: (FliPprD a e) => FliPprM e (A a TypeQualifier -> E e D)
pprTypeQualifier = define $ \x ->
  case_
    x
    [ unTConst $ text "const"
    , unTVolatile $ text "volatile"
    ]

pprDecl :: (FliPprD a e) => FliPprM e (A a Decl -> E e D)
pprDecl = do
  pExp <- pprExp
  pTypeQualifier <- pprTypeQualifier
  typeQualifierList <- list pTypeQualifier
  identList <- commaSep (`textAs` ident)
  pointer <- define $ \p ->
    case_ p [unPointer $ \qs -> text "*" <> case_ qs [unNil $ text "", unCons $ \_ _ -> typeQualifierList qs <+> text ""]]
  pointerList <- sepByClose "" pointer
  rec pDirectDecl <- define $ \x ->
        case_
          x
          [ unDIdent $ \i -> textAs i ident
          , unDArray $ \d e -> pDirectDecl d <> text "[" <> pExp e <> text "]"
          , unDFunction $ \d args -> pDirectDecl d <> text "(" <> identList args <> text ")"
          , unDArrayUnsized $ \d -> pDirectDecl d <> text "[]"
          , unDDecl $ \d -> parens $ pDecl d
          ]
      pDecl <- define $ \x ->
        case_
          x
          [ unDirectDecl pDirectDecl
          , unDPointer $ \ps d -> pointerList ps <> pDirectDecl d
          ]

  return pDecl

-- data DeclSpecifier = DeclStor StorageClass | DeclSpec TypeSpecifier | DeclQual TypeQualifier
-- deriving (Show, Eq)

-- $(mkUn ''DeclSpecifier)

{-
pprDeclSpecifier :: (FliPprD a e) => FliPprM e (A a DeclSpecifier -> E e D)
pprDeclSpecifier = do
  pTypeSpecifier <- pprTypeSpec
  pTypeQualifier <- pprTypeQualifier
  pStorageClass <- pprStorageClass
  return $ \x ->
    case_
      x
      [ unDeclStor pStorageClass
      , unDeclSpec pTypeSpecifier
      , unDeclQual pTypeQualifier
      ]-}

-- pprAbstractDecl :: (FliPprD a e) => FliPprM e (A a AbsDecl -> E e D)

helpPrint = putStrLn . unlines . map (show . pprProgram')

expDecl :: Decl
expDecl = DPointer [Pointer [TConst, TVolatile]] $ DArrayUnsized $ DIdent "x"

pprTypeSpec :: (FliPprD a e) => FliPprM e (A a TypeSpecifier -> E e D)
pprTypeSpec = do
  pExp <- pprExp
  -- structDecl <- define $ \t ->
  -- struct <- define $ \name decls -> text "struct" <+>. textAs name ident <+>. text "{" <+>. structDeclList decls <+> text "}"
  -- anonStruct <- define $ \decls -> text "struct" <+>. text "{" <+>. structDeclList decls <+>. text "}"
  return $ \x ->
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
      , -- , unTStruct $ \n decls -> struct n decls
        -- , unTAnonStruct $ \decls -> anonStruct decls
        unTName $ \n -> textAs n ident
      ]

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
              identExp f <#> text "("
                <> pExpList args
                <> text ")"
          ]
      pExpList <- list pExp
  return pExp

exp1 :: Exp
exp1 = FunctionCall "f" [LitExp $ IntL $ Int 42, LitExp $ FloatL $ Float 3.14, FunctionCall "g" []]

pprProgram :: Exp -> Doc ann
pprProgram = pprMode (flippr $ fromFunction <$> pprExp)

parseProgram :: [Char] -> Err ann [Exp]
parseProgram = E.parse $ parsingMode (flippr $ fromFunction <$> pprExp)

pprProgram' :: Decl -> Doc ann
pprProgram' = pprMode (flippr $ fromFunction <$> pprDecl)

parseProgram' :: [Char] -> Err ann [Decl]
parseProgram' = E.parse $ parsingMode (flippr $ fromFunction <$> pprDecl)
