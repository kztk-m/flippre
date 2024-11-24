{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Helper (
    mfix,
    ifThenElse,
    list,
    commaSep,
    sepBy,
    sepByClose,
    manyParens,
) where

import Text.FliPpr
import Prelude

-- necessary for recursions within do blocks
mfix :: (Arg (E f) a) => (a -> FliPprM f a) -> FliPprM f a
mfix = mfixF

ifThenElse :: Bool -> t -> t -> t
ifThenElse True t _ = t
ifThenElse False _ f = f

list :: (FliPprD a e, Eq v) => (A a v -> E e D) -> FliPprM e (A a [v] -> E e D)
list p = do
    rec list' <- define $ \xs ->
            case_
                xs
                [ unNil $ text ""
                , unCons $ \t ts ->
                    case_
                        ts
                        [ unNil $ p t
                        , unCons $ \_ _ -> p t <+> list' ts
                        ]
                ]
    return list'

sepBy :: (FliPprD a e, Eq v) => String -> (A a v -> E e D) -> FliPprM e (A a [v] -> E e D)
sepBy comma p = do
    rec commaSep' <- define $ \xs ->
            case_
                xs
                [ unCons $ \t ts ->
                    case_
                        ts
                        [ unNil $ p t
                        , unCons $ \_ _ -> p t <> text comma <+>. commaSep' ts
                        ]
                ]
    return $ \xs ->
        case_
            xs
            [ unNil $ text ""
            , unCons $ \_ _ -> commaSep' xs
            ]

sepByClose :: (FliPprD a e, Eq v) => String -> (A a v -> E e D) -> FliPprM e (A a [v] -> E e D)
sepByClose comma p = do
    rec commaSep' <- define $ \xs ->
            case_
                xs
                [ unCons $ \t ts ->
                    case_
                        ts
                        [ unNil $ p t
                        , unCons $ \_ _ -> p t <> text comma <> commaSep' ts
                        ]
                ]
    return $ \xs ->
        case_
            xs
            [ unNil $ text ""
            , unCons $ \_ _ -> commaSep' xs
            ]

commaSep :: (FliPprD a e, Eq v) => (A a v -> E e D) -> FliPprM e (A a [v] -> E e D)
commaSep = sepBy ","

-- manyParens :: (FliPprE arg exp, Defs exp) => E exp D -> E exp D
manyParens d = local $ do
    rec m <- define $ d <? parens m
    return m