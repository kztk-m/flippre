{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Exp (
    pprExp,
) where

import Helper
import Literals
import Text.FliPpr
import Types
import Prelude

pprExp :: (FliPprD a e) => (A a TypeName -> E e D) -> FliPprM e (A a Exp -> E e D, A a CondExp -> E e D, A a AssignmentExp -> E e D)
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

    return (pExp, pCondExp, pAssignmentExp)
