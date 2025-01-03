{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Helper (
    mfix,
    ifThenElse,
    list,
    inlineList,
    sepBy,
    sepByNonEmpty,
    manyParens,
    NonEmpty (..),
) where

import Text.FliPpr
import Prelude

-- necessary for recursions within do blocks
mfix :: (Arg (E f) a) => (a -> FliPprM f a) -> FliPprM f a
mfix = mfixF

ifThenElse :: Bool -> t -> t -> t
ifThenElse True t _ = t
ifThenElse False _ f = f

{-

cautionary tale about being not linear

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
-}

data NonEmpty a = NCons a (NonEmpty a) | NNil a
    deriving (Show, Eq)

$(mkUn ''NonEmpty)

list :: (FliPprD a e, Eq v) => (A a v -> E e D) -> FliPprM e (A a [v] -> E e D)
list p = do
    rec listNE <- define $ \t ts ->
            case_
                ts
                [ unNil $ p t -- singleton case
                , unCons $ \t' ts' -> p t <> line <> listNE t' ts' -- cons case
                ]
        list' <- define $ \ts ->
            case_
                ts
                [ unNil $ text "" -- empty case
                , unCons $ \t' ts' -> listNE t' ts'
                ]
    return list'

inlineList :: (FliPprD a e, Eq v) => (A a v -> E e D) -> FliPprM e (A a [v] -> E e D)
inlineList p = do
    rec listNE <- define $ \t ts ->
            case_
                ts
                [ unNil $ p t -- singleton case
                , unCons $ \t' ts' -> p t <+> listNE t' ts' -- cons case
                ]
        list' <- define $ \ts ->
            case_
                ts
                [ unNil $ text "" -- empty case
                , unCons $ \t' ts' -> listNE t' ts'
                ]
    return list'

sepBy :: (FliPprD a e, Eq v) => E e D -> (A a v -> E e D) -> FliPprM e (A a [v] -> E e D)
sepBy comma p = do
    rec commaSepNE <- define $ \x xs ->
            case_
                xs
                [ unNil $ p x
                , unCons $ \t ts -> p x <> comma <> commaSepNE t ts
                ]
    return $ \xs ->
        case_
            xs
            [ unNil $ text ""
            , unCons commaSepNE
            ]

sepByNonEmpty :: (FliPprD a e, Eq v) => E e D -> (A a v -> E e D) -> FliPprM e (A a (NonEmpty v) -> E e D)
sepByNonEmpty comma p = do
    rec commaSepNE <- define $ \x xs ->
            case_
                xs
                [ unNNil $ \t -> p x <> comma <> p t
                , unNCons $ \t ts -> p x <> comma <> commaSepNE t ts
                ]
    return $ \xs ->
        case_
            xs
            [ unNNil p
            , unNCons commaSepNE
            ]

{-
sepByClose :: (FliPprD a e, Eq v) => String -> (A a v -> E e D) -> FliPprM e (A a [v] -> E e D)
sepByClose comma p = do
    rec commaSepNE <- define $ \x xs ->
            case_
                xs
                [ unNil $ p x
                , unCons $ \t ts -> p x <> text comma <> commaSepNE t ts
                ]
    return $ \xs ->
        case_
            xs
            [ unCons commaSepNE
            ]
-}
{-
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
            -}

-- TODO: space if necessary

-- manyParens :: (FliPprE arg exp, Defs exp) => E exp D -> E exp D
manyParens d = local $ do
    rec m <- define $ d <? parens m
    return m