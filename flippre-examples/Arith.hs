{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
-- To suppress warnings caused by TH code.
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Control.DeepSeq
import System.CPUTime
import Text.FliPpr
import Text.FliPpr.Grammar.Driver.Earley as E
import Prelude

import Data.Word

import Prettyprinter (Doc)

{-# ANN module "HLint: ignore Avoid lambda using `infix`" #-}
{-# ANN module "HLint: ignore Use section" #-}

ifThenElse :: Bool -> t -> t -> t
ifThenElse True t _ = t
ifThenElse False _ f = f

data Exp
  = Add Exp Exp
  | Mul Exp Exp
  | Sub Exp Exp
  | Div Exp Exp
  | Num Int
  deriving (Eq, Show)

$(mkUn ''Exp)

pExp :: FliPpr (Exp ~> D)
pExp = flippr $ do
  let addD x y = align $ group (x </>. text "+" <+>. y)
  let mulD x y = x <+>. text "*" <+>. align y
  let subD x y = align $ group (x </>. text "-" <+>. y)
  let divD x y = x <+>. text "/" <+>. align y

  let manyParens d = local $ do
        rec m <- share $ d <? parens m
        return m

  rec pprDigit <- define $ \x ->
        case_
          x
          [ is 0 $ text "0"
          , is 1 $ text "1"
          , is 2 $ text "2"
          , is 3 $ text "3"
          , is 4 $ text "4"
          , is 5 $ text "5"
          , is 6 $ text "6"
          , is 7 $ text "7"
          , is 8 $ text "8"
          , is 9 $ text "9"
          ]

  rec pprNum <- define $ \x ->
        case_
          x
          [ lt10 $ \xx -> pprDigit xx
          , dm10 $ \d r -> pprNum d <#> pprDigit r
          ]

  rec ppr <- define $ \k x ->
        manyParens $
          case_
            x
            [ unAdd $ \e1 e2 -> opPrinter (Fixity AssocL 0) addD (flip ppr e1) (flip ppr e2) k
            , unSub $ \e1 e2 -> opPrinter (Fixity AssocL 0) subD (flip ppr e1) (flip ppr e2) k
            , unMul $ \e1 e2 -> opPrinter (Fixity AssocL 1) mulD (flip ppr e1) (flip ppr e2) k
            , unDiv $ \e1 e2 -> opPrinter (Fixity AssocL 1) divD (flip ppr e1) (flip ppr e2) k
            , unNum $ \n -> pprNum n
            ]

  return $ fromFunction (ppr (0 :: Word8))
  where
    mfix = mfixF

    lt10 :: (FliPprE arg exp) => (A arg Int -> E exp r) -> Branch (A arg) (E exp) Int r
    lt10 f = Branch (PartialBij "lt10" (\x -> if x < 10 then Just x else Nothing) Just) f

    dm10 :: (FliPprE arg exp) => (A arg Int -> A arg Int -> E exp r) -> Branch (A arg) (E exp) Int r
    dm10 f =
      PartialBij "dm10" (\x -> if x < 10 then Nothing else Just (divMod x 10)) (\(d, r) -> Just (10 * d + r))
        `Branch` \z -> unpair z f

pprExp :: Exp -> Doc ann
pprExp = pprMode pExp

parseExp :: [Char] -> Err ann [Exp]
parseExp =
  E.parse $ parsingModeWith (CommentSpec Nothing (Just (BlockCommentSpec "/*" "*/" False))) pExp

parseExpP :: [Char] -> IO ()
parseExpP s = case parseExp s of
  Ok r -> print r
  Fail d -> print d

exp1 :: Exp
exp1 = Add (Num 1) (Mul (Num 2) (Num 3))

exp2 :: Exp
exp2 =
  foldr (\x -> if even x then Mul (Num $ x `div` 2) else Add (Num $ x `div` 2)) (Num 0) $
    take 100 $
      cycle [2 .. 21]

exp3 :: Exp
exp3 =
  foldl (\r x -> if even x then Mul r (Num $ x `div` 2) else Add r (Num $ x `div` 2)) (Num 0) $
    take 100 $
      cycle [2 .. 21]

countTime :: String -> IO a -> IO a
countTime str comp = do
  putStrLn $ "Measuring " ++ str ++ "..."
  s <- getCPUTime
  r <- comp
  e <- getCPUTime
  let d = fromIntegral (e - s) / (1000000000 :: Double)
  putStrLn $ "Elapsed: " ++ show d ++ " msec."
  return r

main :: IO ()
main = do
  rnf s1 `seq`
    countTime "Exp1" $
      parseExpP s1
  rnf s2 `seq`
    countTime "Exp2" $
      parseExpP s2
  rnf s3 `seq`
    countTime "Exp3" $
      parseExpP s3
  where
    s1 = show $ pprExp exp1
    s2 = show $ pprExp exp2
    s3 = show $ pprExp exp3
