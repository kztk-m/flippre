{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-missing-deriving-strategies #-}

-- ANSI C Grammar example
--
-- Nils Oskar Nuernbergk, 2025
--
-- This implements an additional example that parses an ANSI C Grammar:
-- See https://www.lysator.liu.se/c/ANSI-C-grammar-y.html
--
-- Because of the lack of straightforward ways to implement greedy parsing,
-- this ambiguously parses ++i as either +(+i) or ++i.
-- Similarly, certain space-less declarators (like const*x) cannot be parsed.

import Exp
import Helper
import Prettyprinter (Doc)
import Text.FliPpr hiding (Exp)
import qualified Text.FliPpr as F
import Text.FliPpr.Grammar.Driver.Earley as E
import qualified Text.FliPpr.QDo as F
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
  (Phased s) =>
  (In v [DeclarationSpecifier] -> F.Exp s v D)
  -> (In v Declarator -> F.Exp s v D)
  -> (In v Exp -> F.Exp s v D)
  -> FliPprM s v (In v Declaration -> F.Exp s v D)
pprDeclaration pDeclarationSpecifierList pDeclarator pAssignmentExp = F.do
  rec pDeclaration <- share $ \x ->
        case_ x [unDeclaration $ \d i -> pDeclarationSpecifierList d <> pInitDeclList i <> text ";"]
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
  (Phased s) =>
  (In v CompoundStatement -> F.Exp s v D)
  -> (In v Declarator -> F.Exp s v D)
  -> (In v (NonEmpty DeclarationSpecifier) -> F.Exp s v D)
  -> (In v (NonEmpty Declaration) -> F.Exp s v D)
  -> FliPprM s v (In v FunctionDefinition -> F.Exp s v D)
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
  share $ \x ->
    case_
      x
      [ unFunctionDefinition $ \s d p c ->
          case_
            s
            [ unNothing $ pFunDef1 d p c
            , unJust $ \l -> pDeclarationSpecifierListNonEmpty l <+> pFunDef1 d p c
            ]
      ]

pprLabeledStatement ::
  (Phased s) =>
  (In v Exp -> F.Exp s v D)
  -> (In v Statement -> F.Exp s v D)
  -> FliPprM s v (In v LabeledStatement -> F.Exp s v D)
pprLabeledStatement pCondExp pStatement = share $ \x ->
  case_
    x
    [ unLStmtIdent $ \i s ->
        nest minBound (line' <> textAs i ident <> text ":")
          <> pStatement s -- minBound because the label should be at the beginning of the line. kind of hacky?
    , unLStmtCase $ \e s ->
        nest (-4) (line' <> text "case" <+> pCondExp e <> text ":")
          <> pStatement s
    , unLStmtDefault $ \s ->
        nest (-4) (line' <> text "default" <> text ":")
          <> pStatement s
    ]

pprCompoundStatement ::
  (Monad m) =>
  (In v (NonEmpty Declaration) -> F.Exp s v D)
  -> (In v [Statement] -> F.Exp s v D)
  -> m (Bool -> In v CompoundStatement -> F.Exp s v D)
pprCompoundStatement pDeclarationList pStatementList = do
  return $ \withinSwitch x ->
    case_
      x
      [ unCompoundStatement $ \d s ->
          text "{"
            <> nest
              (if withinSwitch then 8 else 4)
              ( case_ d [unNothing $ text "", unJust $ \l -> line' <> pDeclarationList l] <> pStatementList s
              )
              </>. text "}"
      ]

pprSelectionStatement ::
  (Phased s) =>
  (In v Exp -> F.Exp s v D)
  -> (Bool -> Bool -> In v Statement -> F.Exp s v D)
  -> FliPprM s v (In v SelectionStatement -> F.Exp s v D)
pprSelectionStatement pExp pStatement = share $ \x ->
  case_
    x
    [ unSelStmtIfMaybeElse $ \e s m ->
        case_
          m
          [ unNothing $
              text "if"
                <+>. parens (pExp e)
                <+>. pStatement False False s
          , unJust $ \s' ->
              text "if"
                <+>. parens (pExp e)
                <+>. pStatement False True s -- insert space after compound statement
                <> text "else"
                  <+>. pStatement False False s'
          ]
    , unSelStmtSwitch $ \e s -> text "switch" <+>. parens (pExp e) <+> pStatement True False s
    ]

pprIterationStatement :: (Phased s) => (In v Statement -> F.Exp s v D) -> (In v Exp -> F.Exp s v D) -> FliPprM s v (In v IterationStatement -> F.Exp s v D)
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
                <+>. case_
                  i2
                  [ unNothing $ text ";"
                  , unJust $ \e -> pExp e <> text ";"
                  ]
                <> case_
                  i3
                  [ unNothing $ text ""
                  , unJust $ \e -> space <> pExp e
                  ]
            )
          <+>. pStatement s
    ]

pprJumpStatement :: (Phased s) => (In v Exp -> F.Exp s v D) -> FliPprM s v (In v JumpStatement -> F.Exp s v D)
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

pprProgram :: (Phased s) => FliPprM s v (In v Program -> F.Exp s v D)
pprProgram = F.do
  rec (pExp, pCondExp, pAssignmentExp) <- pprExp pTypeName
      (pTypeName, pDeclarator, pDeclarationSpecifierList, pDeclarationSpecifierListNonEmpty) <- pprTypes pCondExp
  rec pDeclaration <- pprDeclaration pDeclarationSpecifierList pDeclarator pAssignmentExp
      pDeclarationList <- sepByNonEmpty line pDeclaration
      pFunDef <- pprFunDef (pCompoundStatement False) pDeclarator pDeclarationSpecifierListNonEmpty pDeclarationList
      -- statements
      pStatement <- share $ \shouldIndent insertLineAfter withinSwitch insertSpaceAfterCompound x ->
        case_
          x
          [ unStmtLabeled pLabeledStatement
          , otherwiseP $ pStatementLineBefore shouldIndent insertLineAfter withinSwitch insertSpaceAfterCompound
          ]
      pStatementLineBefore <- share $ \shouldIndent insertLineAfter withinSwitch insertSpaceAfterCompound x ->
        case_
          x
          [ unStmtCompound $ (\x -> pCompoundStatement withinSwitch x <> if insertSpaceAfterCompound then text "" <+>. text "" else text "") -- add space if else comes next
          , otherwiseP $ pStatement' shouldIndent insertLineAfter
          ]
      pStatement' <- share $ \shouldIndent insertLineAfter x ->
        if shouldIndent
          then nest 4 (line' <> pStatementInner x) <> (if insertLineAfter then line' else text "")
          else line' <> pStatementInner x
      pStatementInner <- share $ \x ->
        case_
          x
          [ unStmtExp $ \e ->
              case_
                e
                [ unNothing $ text ";"
                , unJust $ \e' -> pExp e' <> text ";"
                ]
          , unStmtSel pSelectionStatement
          , unStmtIter pIterationStatement
          , unStmtJump pJumpStatement
          ]
      pStatementList <- sepBy (text "") (pStatement False False False False)
      pLabeledStatement <- pprLabeledStatement pCondExp (pStatement False False False False)
      pCompoundStatement <- pprCompoundStatement pDeclarationList pStatementList
      pSelectionStatement <- pprSelectionStatement pExp (pStatement True True)
      pIterationStatement <- pprIterationStatement (pStatement True False False False) pExp
      pJumpStatement <- pprJumpStatement pExp -- could technically be in the block above but is here for clarity
  pExternalDeclaration <- share $ \x ->
    case_
      x
      [ unExtDecl $ \d -> pDeclaration d
      , unFunDef $ \f -> pFunDef f
      ]
  sepBy (line' <> line') pExternalDeclaration

test :: String
test = "int main ( ) { callSomeFunction(); label: if (true) goto label; return 0; }"

printProgram :: Program -> Doc ann
printProgram = pprMode (flippr @Explicit $ fromFunction <$> pprProgram)

parseProgram :: [Char] -> Err ann [Program]
parseProgram = E.parse $ parsingModeWith (CommentSpec (Just "//") (Just (BlockCommentSpec "/*" "*/" False))) (flippr @Explicit $ fromFunction <$> pprProgram)

testPrint :: IO ()
testPrint = do
  let (Ok parsed) = parseProgram test
  putStrLn $ "Parsed: " ++ show parsed
  mapM_ (print . printProgram) parsed
  putStrLn $ "Done, parsed " ++ show (length parsed) ++ " programs"

main :: IO ()
main = testPrint