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

pprAssignmentOp :: (FliPprD a e) => FliPprM e (A a AssignmentOp -> E e D)
pprAssignmentOp =
    share $ \x ->
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

pprUnaryOp :: (FliPprD a e) => FliPprM e (A a UnaryOp -> E e D)
pprUnaryOp = share $ \x ->
    case_
        x
        [ unAddress $ text "&"
        , unIndirection $ text "*"
        , unPlus $ text "+"
        , unMinus $ text "-"
        , unBitwiseNot $ text "~"
        , unLogicalNot $ text "!"
        ]

pprExp :: (FliPprD a e) => (A a TypeName -> E e D) -> FliPprM e (A a Exp -> E e D, A a Exp -> E e D, A a Exp -> E e D)
pprExp pTypeName = do
    lit <- pprLit
    pAssignmentOp <- pprAssignmentOp
    pUnaryOp <- pprUnaryOp
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
                [ unLogicalOr $ \e1 e2 -> align $ group $ pLogicalOrExp e1 </>. text "||" <+>. pLogicalAndExp e2
                , otherwiseP pLogicalAndExp
                ]
        pLogicalAndExp <- share $ \x ->
            case_
                x
                [ unLogicalAnd $ \e1 e2 -> align $ group $ pLogicalAndExp e1 </>. text "&&" <+>. pInclusiveOrExp e2
                , otherwiseP pInclusiveOrExp
                ]
        pInclusiveOrExp <- share $ \x ->
            case_
                x
                [ unBitewiseOr $ \e1 e2 -> pInclusiveOrExp e1 <+>. text "|" <+>. pExclusiveOrExp e2
                , otherwiseP pExclusiveOrExp
                ]
        pExclusiveOrExp <- share $ \x ->
            case_
                x
                [ unBitewiseXor $ \e1 e2 -> pExclusiveOrExp e1 <+>. text "^" <+>. pAndExp e2
                , otherwiseP pAndExp
                ]
        pAndExp <- share $ \x ->
            case_
                x
                [ unBitewiseAnd $ \e1 e2 -> pAndExp e1 <+>. text "&" <+>. pEqualityExp e2
                , otherwiseP pEqualityExp
                ]
        pEqualityExp <- share $ \x ->
            case_
                x
                [ unEq $ \e1 e2 -> align $ group $ pEqualityExp e1 </>. text "==" <+>. pRelationalExp e2
                , unNeq $ \e1 e2 -> align $ group $ pEqualityExp e1 </>. text "!=" <+>. pRelationalExp e2
                , otherwiseP pRelationalExp
                ]
        pRelationalExp <- share $ \x ->
            case_
                x
                [ unLt $ \e1 e2 -> align $ group $ pRelationalExp e1 </>. text "<" <+>. pShiftExp e2
                , unGt $ \e1 e2 -> align $ group $ pRelationalExp e1 </>. text ">" <+>. pShiftExp e2
                , unLe $ \e1 e2 -> align $ group $ pRelationalExp e1 </>. text "<=" <+>. pShiftExp e2
                , unGe $ \e1 e2 -> align $ group $ pRelationalExp e1 </>. text ">=" <+>. pShiftExp e2
                , otherwiseP pShiftExp
                ]
        pShiftExp <- share $ \x ->
            case_
                x
                [ unShiftLeft $ \e1 e2 -> pShiftExp e1 <+>. text "<<" <+>. pAdditiveExp e2
                , unShiftRight $ \e1 e2 -> pShiftExp e1 <+>. text ">>" <+>. pAdditiveExp e2
                , otherwiseP pAdditiveExp
                ]
        pAdditiveExp <- share $ \x ->
            case_
                x
                [ unAdd $ \e1 e2 -> align $ group $ pAdditiveExp e1 </>. text "+" <+>. pMultiplicativeExp e2
                , unSub $ \e1 e2 -> align $ group $ pAdditiveExp e1 </>. text "-" <+>. pMultiplicativeExp e2
                , otherwiseP pMultiplicativeExp
                ]
        pMultiplicativeExp <- share $ \x ->
            case_
                x
                [ unMul $ \e1 e2 -> pMultiplicativeExp e1 <+>. text "*" <+>. pCastExp e2
                , unDiv $ \e1 e2 -> pMultiplicativeExp e1 <+>. text "/" <+>. pCastExp e2
                , unMod $ \e1 e2 -> pMultiplicativeExp e1 <+>. text "%" <+>. pCastExp e2
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
                  unPostfixCall $ \e args -> pPostfixExp e <#> parens (pAssignmentList args)
                , unPostfixArrayIndex $ \e1 e2 -> pPostfixExp e1 <#> text "[" <> pExp e2 <> text "]"
                , unPostfixDot $ \e s -> pPostfixExp e <#> text "." <#> textAs s ident
                , unPostfixArrow $ \e s -> pPostfixExp e <#> text "->" <#> textAs s ident
                , unPostfixInc $ \e -> pPostfixExp e <#> text "++"
                , unPostfixDec $ \e -> pPostfixExp e <#> text "--"
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
