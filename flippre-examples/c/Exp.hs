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

pprExp :: (FliPprD a e) => (A a TypeName -> E e D) -> FliPprM e (A a Exp -> E e D, A a Exp -> E e D, A a Exp -> E e D)
pprExp pTypeName = do
    lit <- pprLit
    pAssignmentOp <- share $ \x ->
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
    pUnaryOp <- share $ \x ->
        case_
            x
            [ unAddress $ text "&"
            , unIndirection $ text "*"
            , unPlus $ text "+"
            , unMinus $ text "-"
            , unBitwiseNot $ text "~"
            , unLogicalNot $ text "!"
            ]
    identExp <- share $ \x -> textAs x ident
    rec pExp <- share $ \x ->
            case_
                x
                [ unComma $ \e1 e2 -> align $ group $ pExp e1 </>. text "," <+>. pAssignmentExp e2
                , otherwiseP pAssignmentExp
                ]
        pAssignmentExp <- share $ \x ->
            case_
                x
                [ unAssign $ \op e1 e2 -> pUnaryExp e1 <+>. pAssignmentOp op <+>. pAssignmentExp e2
                , otherwiseP pCondExp
                ]
        pCondExp <- share $ \x ->
            case_
                x
                [ unTernary $ \e1 e2 e3 -> pLogicalOrExp e1 <+> align (vsep [text "?" <+>. pExp e2, text ":" <+>. pCondExp e3])
                , otherwiseP pLogicalOrExp
                ]
        pLogicalOrExp <- share $ \x ->
            case_
                x
                [ unLogicalOrExpOr $ \e1 e2 -> align $ group $ pLogicalOrExp e1 </>. text "||" <+>. pLogicalAndExp e2
                , otherwiseP pLogicalAndExp
                ]
        pLogicalAndExp <- share $ \x ->
            case_
                x
                [ unLogicalAndExpAnd $ \e1 e2 -> align $ group $ pLogicalAndExp e1 </>. text "&&" <+>. pInclusiveOrExp e2
                , otherwiseP pInclusiveOrExp
                ]
        pInclusiveOrExp <- share $ \x ->
            case_
                x
                [ unInclusiveOrExpOr $ \e1 e2 -> pInclusiveOrExp e1 <+>. text "|" <+>. pExclusiveOrExp e2
                , otherwiseP pExclusiveOrExp
                ]
        pExclusiveOrExp <- share $ \x ->
            case_
                x
                [ unExclusiveOrExpXor $ \e1 e2 -> pExclusiveOrExp e1 <+>. text "^" <+>. pAndExp e2
                , otherwiseP pAndExp
                ]
        pAndExp <- share $ \x ->
            case_
                x
                [ unAndExpAnd $ \e1 e2 -> pAndExp e1 <+>. text "&" <+>. pEqualityExp e2
                , otherwiseP pEqualityExp
                ]
        pEqualityExp <- share $ \x ->
            case_
                x
                [ unEqualityExpEq $ \e1 e2 -> align $ group $ pEqualityExp e1 </>. text "==" <+>. pRelationalExp e2
                , unEqualityExpNeq $ \e1 e2 -> align $ group $ pEqualityExp e1 </>. text "!=" <+>. pRelationalExp e2
                , otherwiseP pRelationalExp
                ]
        pRelationalExp <- share $ \x ->
            case_
                x
                [ unRelationalExpLt $ \e1 e2 -> align $ group $ pRelationalExp e1 </>. text "<" <+>. pShiftExp e2
                , unRelationalExpGt $ \e1 e2 -> align $ group $ pRelationalExp e1 </>. text ">" <+>. pShiftExp e2
                , unRelationalExpLe $ \e1 e2 -> align $ group $ pRelationalExp e1 </>. text "<=" <+>. pShiftExp e2
                , unRelationalExpGe $ \e1 e2 -> align $ group $ pRelationalExp e1 </>. text ">=" <+>. pShiftExp e2
                , otherwiseP pShiftExp
                ]
        pShiftExp <- share $ \x ->
            case_
                x
                [ unShiftExpLeft $ \e1 e2 -> pShiftExp e1 <+>. text "<<" <+>. pAdditiveExp e2
                , unShiftExpRight $ \e1 e2 -> pShiftExp e1 <+>. text ">>" <+>. pAdditiveExp e2
                , otherwiseP pAdditiveExp
                ]
        pAdditiveExp <- share $ \x ->
            case_
                x
                [ unAdditiveExpPlus $ \e1 e2 -> align $ group $ pAdditiveExp e1 </>. text "+" <+>. pMultiplicativeExp e2
                , unAdditiveExpMinus $ \e1 e2 -> align $ group $ pAdditiveExp e1 </>. text "-" <+>. pMultiplicativeExp e2
                , otherwiseP pMultiplicativeExp
                ]
        pMultiplicativeExp <- share $ \x ->
            case_
                x
                [ unMultiplicativeExpMul $ \e1 e2 -> pMultiplicativeExp e1 <+>. text "*" <+>. pCastExp e2
                , unMultiplicativeExpDiv $ \e1 e2 -> pMultiplicativeExp e1 <+>. text "/" <+>. pCastExp e2
                , unMultiplicativeExpMod $ \e1 e2 -> pMultiplicativeExp e1 <+>. text "%" <+>. pCastExp e2
                , otherwiseP pCastExp
                ]
        pCastExp <- share $ \x ->
            case_
                x
                [ unCast $ \t e -> parens (pTypeName t) <+>. pCastExp e
                , otherwiseP pUnaryExp
                ]
        pUnaryExp <- share $ \x ->
            case_
                x
                [ unInc $ \e -> text "++" <#> pUnaryExp e
                , unDec $ \e -> text "--" <#> pUnaryExp e
                , unUnaryOp $ \op e -> pUnaryOp op <#> pCastExp e
                , unSizeofExp $ \e -> text "sizeof" <> parens (pUnaryExp e)
                , unSizeofType $ \t -> text "sizeof" <> parens (pTypeName t)
                , otherwiseP pPostfixExp
                ]
        pAssignmentList <- sepBy (text "," <> space) pAssignmentExp
        pPostfixExp <- share $ \x ->
            case_
                x
                [ -- hardcats necessary
                  unPostfixExpCall $ \e args -> pPostfixExp e <#> parens (pAssignmentList args)
                , unPostfixExpArray $ \e1 e2 -> pPostfixExp e1 <#> text "[" <> pExp e2 <> text "]"
                , unPostfixExpDot $ \e s -> pPostfixExp e <#> text "." <#> textAs s ident
                , unPostfixExpArrow $ \e s -> pPostfixExp e <#> text "->" <#> textAs s ident
                , unPostfixExpInc $ \e -> pPostfixExp e <#> text "++"
                , unPostfixExpDec $ \e -> pPostfixExp e <#> text "--"
                , otherwiseP pPrimaryExp
                ]
        pPrimaryExp <-
            share $ \x ->
                case_
                    x
                    [ unLitExp $ \l -> lit l
                    , unIdentExp $ \i -> identExp i
                    , otherwiseP $ \e -> parens (pExp e)
                    ]

    return (pExp, pCondExp, pAssignmentExp)
