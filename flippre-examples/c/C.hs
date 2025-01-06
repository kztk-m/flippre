{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

import Exp
import Helper
import Literals
import Prettyprinter (Doc)
import Text.FliPpr
import Text.FliPpr.Grammar.Driver.Earley as E
import TypeSpecifier
import Types
import Prelude

type Program = [ExternalDeclaration]

data ExternalDeclaration = ExtDecl Declaration | FunDef FunctionDefinition
  deriving (Show, Eq)

data FunctionDefinition = FunctionDefinition (Maybe (NonEmpty DeclarationSpecifier)) Declarator (Maybe (NonEmpty Declaration)) (Maybe CompoundStatement)
  deriving (Show, Eq)

data Declaration = Declaration [DeclarationSpecifier] [InitDeclarator]
  deriving (Show, Eq)

data InitDeclarator = InitDeclarator Declarator (Maybe Initializer)
  deriving (Show, Eq)

data Initializer = InitExp Exp | InitList (NonEmpty Initializer)
  deriving (Show, Eq)

data Statement
  = StmtLabeled LabeledStatement
  | StmtCompound CompoundStatement
  | StmtExp (Maybe Exp)
  | StmtSel SelectionStatement
  | StmtIter IterationStatement
  | StmtJump JumpStatement
  deriving (Show, Eq)

data LabeledStatement
  = LStmtIdent String Statement
  | LStmtCase Exp Statement
  | LStmtDefault Statement
  deriving (Show, Eq)

data CompoundStatement = CompoundStatement (Maybe (NonEmpty Declaration)) [Statement]
  deriving (Show, Eq)

data SelectionStatement
  = SelStmtIfMaybeElse Exp Statement (Maybe Statement)
  | SelStmtSwitch Exp Statement
  deriving (Show, Eq)

data IterationStatement
  = IterStmtWhile Exp Statement
  | IterStmtDoWhile Statement Exp
  | IterStmtFor (Maybe Exp) (Maybe Exp) (Maybe Exp) Statement
  deriving (Show, Eq)

data JumpStatement
  = JumpStmtGoto String
  | JumpStmtContinue
  | JumpStmtBreak
  | JumpStmtReturn (Maybe Exp)
  deriving (Show, Eq)

$(mkUn ''ExternalDeclaration)
$(mkUn ''FunctionDefinition)
$(mkUn ''Declaration)
$(mkUn ''InitDeclarator)
$(mkUn ''Initializer)
$(mkUn ''Statement)
$(mkUn ''LabeledStatement)
$(mkUn ''CompoundStatement)
$(mkUn ''SelectionStatement)
$(mkUn ''IterationStatement)
$(mkUn ''JumpStatement)
$(mkUn ''Maybe)

pprDeclaration ::
  (FliPprD a e) =>
  (A a [DeclarationSpecifier] -> E e D) ->
  (A a Declarator -> E e D) ->
  (A a Exp -> E e D) ->
  FliPprM e (A a Declaration -> E e D)
pprDeclaration pDeclarationSpecifierList pDeclarator pAssignmentExp = do
  rec pDeclaration <- share $ \x ->
        case_ x [unDeclaration $ \d i -> pDeclarationSpecifierList d <+> pInitDeclList i <> text ";"]
      pInitDecl <- share $ \x ->
        case_
          x
          [ unInitDeclarator $ \d i ->
              case_
                i
                [ unNothing $ pDeclarator d
                , unJust $ \i' -> pDeclarator d <+>. text "=" <+>. pInitializer i'
                ]
          ]
      pInitializer <- share $ \x ->
        case_
          x
          [ unInitExp $ \e -> pAssignmentExp e
          , unInitList $ \l -> text "{" <+>. pInitListNonEmpty l <> (text "" <? text ",") <+>. text "}"
          ]
      pInitListNonEmpty <- sepByNonEmpty (text "," <+>. text "") pInitializer
      pInitDeclList <- sepBy (text "," <+>. text "") pInitDecl
  return pDeclaration

pprFunDef ::
  (FliPprD a e) =>
  (A a CompoundStatement -> E e D) ->
  (A a Declarator -> E e D) ->
  (A a (NonEmpty DeclarationSpecifier) -> E e D) ->
  (A a (NonEmpty Declaration) -> E e D) ->
  FliPprM e (A a FunctionDefinition -> E e D)
pprFunDef pCompoundStatement pDeclarator pDeclarationSpecifierListNonEmpty pDeclarationList = do
  -- seperated into 3 different functions to get spacing right
  pFunDef2 <- share $ \c ->
    case_
      c
      [ unNothing $ text ";"
      , unJust $ \s -> text "" <+>. pCompoundStatement s
      ]
  pFunDef1 <- share $ \d p c ->
    pDeclarator d
      <> case_
        p
        [ unNothing $ pFunDef2 c
        , unJust $ \l -> pDeclarationList l <+> pFunDef2 c
        ]
  pFunDef <- share $ \x ->
    case_
      x
      [ unFunctionDefinition $ \s d p c ->
          case_
            s
            [ unNothing $ pFunDef1 d p c
            , unJust $ \l -> pDeclarationSpecifierListNonEmpty l <+> pFunDef1 d p c
            ]
      ]
  return pFunDef

pprLabeledStatement ::
  (FliPprD a e) =>
  (A a Exp -> E e D) ->
  (A a Statement -> E e D) ->
  FliPprM e (A a LabeledStatement -> E e D)
pprLabeledStatement pCondExp pStatement = share $ \x ->
  case_
    x
    [ unLStmtIdent $ \i s -> textAs i ident <> text ":" <+>. pStatement s -- TODO: spacing on this
    , unLStmtCase $ \e s -> text "case" <+> pCondExp e <> text ":" <> line <> pStatement s -- TODO
    , unLStmtDefault $ \s -> text "default" <> text ":" <+>. pStatement s
    ]

pprCompoundStatement ::
  (FliPprD a e) =>
  (A a (NonEmpty Declaration) -> E e D) ->
  (A a [Statement] -> E e D) ->
  FliPprM e (A a CompoundStatement -> E e D)
pprCompoundStatement pDeclarationList pStatementList = share $ \x ->
  case_
    x
    [ unCompoundStatement $ \d s ->
        text "{"
          <> nest
            4
            ( case_ d [unNothing $ text "", unJust $ \l -> line <> pDeclarationList l] <> line <> pStatementList s
            )
          <> line'
          <> text "}"
    ]

pprSelectionStatement ::
  (FliPprD a e) =>
  (A a Exp -> E e D) ->
  (A a Statement -> E e D) ->
  FliPprM e (A a SelectionStatement -> E e D)
pprSelectionStatement pExp pStatement = share $ \x ->
  case_
    x
    [ unSelStmtIfMaybeElse $ \e s m ->
        case_
          m
          [ unNothing $
              text "if"
                <+>. parens (pExp e)
                <+>. pStatement s
          , unJust $ \s' ->
              text "if"
                <+>. parens (pExp e)
                <+>. pStatement s
                <+>. text "else"
                <+> pStatement s'
          ]
    , unSelStmtSwitch $ \e s -> text "switch" <+>. parens (pExp e) <+> pStatement s
    ]

pprIterationStatement ::
  (FliPprD a e) =>
  (A a Statement -> E e D) ->
  (A a Exp -> E e D) ->
  FliPprM e (A a IterationStatement -> E e D)
pprIterationStatement pStatement pExp = share $ \x ->
  case_
    x
    [ unIterStmtWhile $ \e s -> text "while" <+>. parens (pExp e) <+>. pStatement s
    , unIterStmtDoWhile $ \s e -> text "do" <+> pStatement s <+>. text "while" <+>. parens (pExp e) <> text ";"
    , unIterStmtFor $ \i1 i2 i3 s ->
        text "for"
          <+>. parens
            ( case_
                i1
                [ unNothing $ text ";"
                , unJust $ \e -> pExp e <> text ";"
                ]
                <> case_
                  i2
                  [ unNothing $ text ";"
                  , unJust $ \e -> pExp e <> text ";"
                  ]
                <> case_
                  i3
                  [ unNothing $ text ""
                  , unJust $ \e -> pExp e
                  ]
            )
          <+>. pStatement s
    ]

pprJumpStatement ::
  (FliPprD a e) =>
  (A a Exp -> E e D) ->
  FliPprM e (A a JumpStatement -> E e D)
pprJumpStatement pExp = share $ \x ->
  case_
    x
    [ unJumpStmtGoto $ \i -> text "goto" <+> textAs i ident <> text ";"
    , unJumpStmtContinue $ text "continue" <> text ";"
    , unJumpStmtBreak $ text "break" <> text ";"
    , unJumpStmtReturn $ \e ->
        case_
          e
          [ unNothing $ text "return" <> text ";"
          , unJust $ \e' -> text "return" <+> pExp e' <> text ";"
          ]
    ]

pprProgram :: (FliPprD a e) => FliPprM e (A a Program -> E e D)
pprProgram = do
  rec (pExp, pCondExp, pAssignmentExp) <- pprExp pTypeName
      (pTypeName, pDeclarator, pDeclarationSpecifierList, pDeclarationSpecifierListNonEmpty) <- pprTypes pCondExp
  rec pDeclaration <- pprDeclaration pDeclarationSpecifierList pDeclarator pAssignmentExp
      pDeclarationList <- sepByNonEmpty line pDeclaration
      pFunDef <- pprFunDef pCompoundStatement pDeclarator pDeclarationSpecifierListNonEmpty pDeclarationList
      -- statements
      pStatement <- share $ \x ->
        case_
          x
          [ unStmtLabeled pLabeledStatement
          , unStmtCompound pCompoundStatement
          , unStmtExp $ \e ->
              case_
                e
                [ unNothing $ text ";"
                , unJust $ \e' -> pExp e' <> text ";"
                ]
          , unStmtSel pSelectionStatement
          , unStmtIter pIterationStatement
          , unStmtJump pJumpStatement
          ]
      pStatementList <- list pStatement
      pLabeledStatement <- pprLabeledStatement pCondExp pStatement
      pCompoundStatement <- pprCompoundStatement pDeclarationList pStatementList
      pSelectionStatement <- pprSelectionStatement pExp pStatement
      pIterationStatement <- pprIterationStatement pStatement pExp
      pJumpStatement <- pprJumpStatement pExp -- could technically be in the block above but is here for clarity
  pExternalDeclaration <- share $ \x ->
    case_
      x
      [ unExtDecl $ \d -> pDeclaration d
      , unFunDef $ \f -> pFunDef f
      ]
  list pExternalDeclaration

test :: String
test = "void processArray(int *arr, int size) { int i, choice; int index; int value; printf(abc); printf(def); scanf(a, &choice); switch (choice) { case 1: printf(string); for (i = 1; i < 10; i++) { printf(string, *(arr + i)); } break; case 2: printf(string, size - 1); scanf(string, &index); if (index < 0 || index >= size) { printf(string); goto menu;  } scanf(string, &value); *(arr + index) = value; printf(string); break; case 3: printf(string); return; default: printf(string); goto menu;  } menu: processArray(arr, size); } int main() { int array[5] = {10, 20, 30, 40, 50} ; printf(welcome_string); while( x <= 2) { while(x >= 2 ) hello();} processArray(array, 5); do { test(); } while (x >= 0); return 0; }"

printProgram :: Program -> Doc ann
printProgram = pprMode (flippr $ fromFunction <$> pprProgram)

parseProgram :: [Char] -> Err ann [Program]
parseProgram = E.parse $ parsingMode (flippr $ fromFunction <$> pprProgram)
