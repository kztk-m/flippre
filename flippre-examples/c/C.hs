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

data FunctionDefinition = FunctionDefinition (Maybe (NonEmpty DeclSpecifier)) Decl (Maybe (NonEmpty Declaration)) (Maybe CompoundStatement)
  deriving (Show, Eq)

data CompoundStatement = CompoundStatement (Maybe (NonEmpty Declaration)) [Statement]
  deriving (Show, Eq)

data Declaration = Declaration [DeclSpecifier] [InitDeclarator]
  deriving (Show, Eq)

data InitDeclarator = InitDecl Decl (Maybe Initializer)
  deriving (Show, Eq)

data Initializer = InitExp AssignmentExp | InitList (NonEmpty Initializer)
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
  | LStmtCase CondExp Statement
  | LStmtDefault Statement
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
$(mkUn ''CompoundStatement)
$(mkUn ''Declaration)
$(mkUn ''InitDeclarator)
$(mkUn ''Initializer)
$(mkUn ''Statement)
$(mkUn ''LabeledStatement)
$(mkUn ''SelectionStatement)
$(mkUn ''IterationStatement)
$(mkUn ''JumpStatement)
$(mkUn ''Maybe)

pprProgram :: (FliPprD a e) => FliPprM e (A a Program -> E e D)
pprProgram = do
  rec (pExp, pCondExp, pAssignmentExp) <- pprExp pTypeName
      (pTypeName, pDecl, pDeclSpecList, pDeclSpecListNonEmpty) <- pprTypes pCondExp
  rec pExternalDeclaration <- share $ \x ->
        case_
          x
          [ unExtDecl $ \d -> pDeclaration d
          , unFunDef $ \f -> pFunDef f
          ]
      pDeclaration <- share $ \x ->
        case_ x [unDeclaration $ \d i -> pDeclSpecList d <+> pInitDeclList i <> text ";"]
      pDeclarationList <- sepByNonEmpty line pDeclaration
      pInitDecl <- share $ \x ->
        case_
          x
          [ unInitDecl $ \d i ->
              case_
                i
                [ unNothing $ pDecl d
                , unJust $ \i' -> pDecl d <+>. text "=" <+>. pInitializer i'
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
      -- seperated into three different functions to get spacing right
      pFunDef <- share $ \x ->
        case_
          x
          [ unFunctionDefinition $ \s d p c ->
              case_
                s
                [ unNothing $ pFunDef1 d p c
                , unJust $ \l -> pDeclSpecListNonEmpty l <+> pFunDef1 d p c
                ]
          ]
      pFunDef1 <- share $ \d p c ->
        pDecl d
          <> case_
            p
            [ unNothing $ pFunDef2 c
            , unJust $ \l -> pDeclarationList l <+> pFunDef2 c
            ]
      pFunDef2 <- share $ \c ->
        case_
          c
          [ unNothing $ text ";"
          , unJust $ \s -> text "" <+>. pCompoundStatement s
          ]
      pCompoundStatement <- share $ \x ->
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
      pStatementList <- list pStatement
      pStatement <- share $ \x ->
        case_
          x
          [ unStmtLabeled $ \l -> pLabeledStatement l
          , unStmtCompound $ \c -> pCompoundStatement c
          , unStmtExp $ \e ->
              case_
                e
                [ unNothing $ text ";"
                , unJust $ \e' -> pExp e' <> text ";"
                ]
          , unStmtSel $ \s -> pSelectionStatement s
          , unStmtIter $ \i -> pIterationStatement i
          , unStmtJump $ \j -> pJumpStatement j
          ]
      pLabeledStatement <- share $ \x ->
        case_
          x
          [ unLStmtIdent $ \i s -> textAs i ident <> text ":" <+>. pStatement s -- TODO: spacing on this
          , unLStmtCase $ \e s -> text "case" <+> pCondExp e <> text ":" <> line <> pStatement s -- TODO
          , unLStmtDefault $ \s -> text "default" <> text ":" <+>. pStatement s
          ]
      pSelectionStatement <- share $ \x ->
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
      pIterationStatement <- share $ \x ->
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
      pJumpStatement <- share $ \x ->
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
  list pExternalDeclaration

test :: String
test = "void processArray(int *arr, int size) { int i, choice; int index; int value; printf(abc); printf(def); scanf(a, &choice); switch (choice) { case 1: printf(string); for (i = 1; i < 10; i++) { printf(string, *(arr + i)); } break; case 2: printf(string, size - 1); scanf(string, &index); if (index < 0 || index >= size) { printf(string); goto menu;  } scanf(string, &value); *(arr + index) = value; printf(string); break; case 3: printf(string); return; default: printf(string); goto menu;  } menu: processArray(arr, size); } int main() { int array[5] = {10, 20, 30, 40, 50} ; printf(welcome_string); while( x <= 2) { while(x >= 2 ) hello();} processArray(array, 5); do { test(); } while (x >= 0); return 0; }"

-- test = "int main() { return 0; }"

pExp :: (FliPprD a e) => FliPprM e (A a Exp -> E e D)
pExp = do
  rec (pExp, pCondExp, pAssignmentExp) <- pprExp pTypeName
      (pTypeName, pDecl, pDeclSpecList, pDeclSpecListNonEmpty) <- pprTypes pCondExp
  return pExp

printExp :: Exp -> Doc ann
printExp = pprMode (flippr $ fromFunction <$> pExp)

printProgram :: Program -> Doc ann
printProgram = pprMode (flippr $ fromFunction <$> pprProgram)

parseProgram :: [Char] -> Err ann [Program]
parseProgram = E.parse $ parsingMode (flippr $ fromFunction <$> pprProgram)

x :: Program
x =
  [ FunDef (FunctionDefinition (Just (NNil (DeclSpec TVoid))) (DirectDecl (DProto (DIdent "processArray") (Fixed (NCons (PDecl (NNil (DeclSpec TInt)) (DPointer (NNil (Pointer [])) (DIdent "arr"))) (NNil (PDecl (NNil (DeclSpec TInt)) (DirectDecl (DIdent "size")))))))) Nothing (Just (CompoundStatement (Just (NCons (Declaration [DeclSpec TInt] [InitDecl (DirectDecl (DIdent "i")) Nothing, InitDecl (DirectDecl (DIdent "choice")) Nothing]) (NCons (Declaration [DeclSpec TInt] [InitDecl (DirectDecl (DIdent "index")) Nothing]) (NNil (Declaration [DeclSpec TInt] [InitDecl (DirectDecl (DIdent "value")) Nothing]))))) [StmtExp (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpCall (PrimaryExp (IdentExp "printf")) [CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "abc")))))))))))))))]))))))))))))))))), StmtExp (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpCall (PrimaryExp (IdentExp "printf")) [CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "def")))))))))))))))]))))))))))))))))), StmtExp (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpCall (PrimaryExp (IdentExp "scanf")) [CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "a"))))))))))))))), CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (UnaryOp Address (Unary (PostfixExp (PrimaryExp (IdentExp "choice")))))))))))))))))]))))))))))))))))), StmtSel (SelStmtSwitch (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "choice"))))))))))))))))) (StmtCompound (CompoundStatement Nothing [StmtLabeled (LStmtCase (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (LitExp (IntL (Int 1))))))))))))))))) (StmtExp (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpCall (PrimaryExp (IdentExp "printf")) [CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "string")))))))))))))))]))))))))))))))))))), StmtIter (IterStmtFor (Just (Assignment (Assign AssignOp (PostfixExp (PrimaryExp (IdentExp "i"))) (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (LitExp (IntL (Int 1))))))))))))))))))))) (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (RelationalExpLt (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "i")))))))) (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (LitExp (IntL (Int 10)))))))))))))))))))) (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpInc (PrimaryExp (IdentExp "i"))))))))))))))))))) (StmtCompound (CompoundStatement Nothing [StmtExp (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpCall (PrimaryExp (IdentExp "printf")) [CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "string"))))))))))))))), CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (UnaryOp Indirection (Unary (PostfixExp (PrimaryExp (Exp (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (AdditiveExpPlus (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "arr")))))) (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "i"))))))))))))))))))))))))))))))))))])))))))))))))))))]))), StmtJump JumpStmtBreak, StmtLabeled (LStmtCase (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (LitExp (IntL (Int 2))))))))))))))))) (StmtExp (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpCall (PrimaryExp (IdentExp "printf")) [CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "string"))))))))))))))), CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (AdditiveExpMinus (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "size")))))) (CastExp (Unary (PostfixExp (PrimaryExp (LitExp (IntL (Int 1)))))))))))))))))]))))))))))))))))))), StmtExp (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpCall (PrimaryExp (IdentExp "scanf")) [CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "string"))))))))))))))), CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (UnaryOp Address (Unary (PostfixExp (PrimaryExp (IdentExp "index")))))))))))))))))]))))))))))))))))), StmtSel (SelStmtIfMaybeElse (Assignment (CondExp (LogicalOrExp (LogicalOrExpOr (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (RelationalExpLt (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "index")))))))) (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (LitExp (IntL (Int 0)))))))))))))))) (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (RelationalExpGe (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "index")))))))) (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "size"))))))))))))))))) (StmtCompound (CompoundStatement Nothing [StmtExp (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpCall (PrimaryExp (IdentExp "printf")) [CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "string")))))))))))))))]))))))))))))))))), StmtJump (JumpStmtGoto "menu")])) Nothing), StmtExp (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpCall (PrimaryExp (IdentExp "scanf")) [CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "string"))))))))))))))), CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (UnaryOp Address (Unary (PostfixExp (PrimaryExp (IdentExp "value")))))))))))))))))]))))))))))))))))), StmtExp (Just (Assignment (Assign AssignOp (UnaryOp Indirection (Unary (PostfixExp (PrimaryExp (Exp (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (AdditiveExpPlus (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "arr")))))) (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "index")))))))))))))))))))))) (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "value"))))))))))))))))))), StmtExp (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpCall (PrimaryExp (IdentExp "printf")) [CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "string")))))))))))))))]))))))))))))))))), StmtJump JumpStmtBreak, StmtLabeled (LStmtCase (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (LitExp (IntL (Int 3))))))))))))))))) (StmtExp (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpCall (PrimaryExp (IdentExp "printf")) [CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "string")))))))))))))))]))))))))))))))))))), StmtJump (JumpStmtReturn Nothing), StmtLabeled (LStmtDefault (StmtExp (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpCall (PrimaryExp (IdentExp "printf")) [CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "string")))))))))))))))]))))))))))))))))))), StmtJump (JumpStmtGoto "menu")]))), StmtLabeled (LStmtIdent "menu" (StmtExp (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpCall (PrimaryExp (IdentExp "processArray")) [CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "arr"))))))))))))))), CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "size")))))))))))))))])))))))))))))))))))])))
  , FunDef (FunctionDefinition (Just (NNil (DeclSpec TInt))) (DirectDecl (DFunction (DIdent "main"))) Nothing (Just (CompoundStatement (Just (NNil (Declaration [DeclSpec TInt] [InitDecl (DirectDecl (DArray (DIdent "array") (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (LitExp (IntL (Int 5))))))))))))))))))) (Just (InitList (NCons (InitExp (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (LitExp (IntL (Int 10))))))))))))))))))) (NCons (InitExp (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (LitExp (IntL (Int 20))))))))))))))))))) (NCons (InitExp (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (LitExp (IntL (Int 30))))))))))))))))))) (NCons (InitExp (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (LitExp (IntL (Int 40))))))))))))))))))) (NNil (InitExp (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (LitExp (IntL (Int 50))))))))))))))))))))))))))]))) [StmtExp (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpCall (PrimaryExp (IdentExp "printf")) [CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "welcome_string")))))))))))))))]))))))))))))))))), StmtExp (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PostfixExpCall (PrimaryExp (IdentExp "processArray")) [CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (IdentExp "array"))))))))))))))), CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (LitExp (IntL (Int 5)))))))))))))))))]))))))))))))))))), StmtJump (JumpStmtReturn (Just (Assignment (CondExp (LogicalOrExp (LogicalAndExp (InclusiveOrExp (ExclusiveOrExp (AndExp (EqualityExp (RelationalExp (ShiftExp (AdditiveExp (MultiplicativeExp (CastExp (Unary (PostfixExp (PrimaryExp (LitExp (IntL (Int 0)))))))))))))))))))))])))
  ]