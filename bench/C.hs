{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecursiveDo #-}

import Text.FliPpr

import qualified Text.FliPpr.Internal.GrammarST as G 
import Text.FliPpr.Driver.Earley (Earley(..))

import System.CPUTime

data Exp = Add Exp Exp
         | Mul Exp Exp
         | Sub Exp Exp
         | Div Exp Exp
         | Num Int
         deriving (Eq , Show)

$(mkUn ''Exp) 


pExp :: FliPpr (Exp :~> D)
pExp = flippr $ do
  let addD x y = align $ group (x </>. text "+" <+>. y)
  let mulD x y = x <+>. text "*" <+>. align y
  let subD x y = align $ group (x </>. text "-" <+>. y)
  let divD x y = x <+>. text "/" <+>. align y

  rec pprDigit <- define $ \x ->
        case_ x
        [ is 0 $ text "0",
          is 1 $ text "1",
          is 2 $ text "2",
          is 3 $ text "3",
          is 4 $ text "4",
          is 5 $ text "5",
          is 6 $ text "6",
          is 7 $ text "7",
          is 8 $ text "8",
          is 9 $ text "9"]
  
  rec pprNum <- define $ \x ->
        case_ x
        [ lt10 $ \x -> pprDigit x,
          dm10 $ \d r -> pprNum d <#> pprDigit r ]
  
  rec ppr <- defines [0,1,2] $ \k x ->
        case_ x
        [ unAdd $ \e1 e2 -> opPrinter (Fixity AssocL 0) addD (flip ppr e1) (flip ppr e2) k,
          unSub $ \e1 e2 -> opPrinter (Fixity AssocL 0) subD (flip ppr e1) (flip ppr e2) k,
          unMul $ \e1 e2 -> opPrinter (Fixity AssocL 1) mulD (flip ppr e1) (flip ppr e2) k,
          unDiv $ \e1 e2 -> opPrinter (Fixity AssocL 1) divD (flip ppr e1) (flip ppr e2) k,
          unNum $ \n -> pprNum n 
          ]

  return $ fromFunction (ppr 0) 
    
  where
    is :: (FliPprE arg exp, Eq c, Show c) => c -> E exp r -> Branch (A arg) (E exp) c r
    is c f = PartialBij ("is " ++ show c)
                       (\x -> if x == c then Just () else Nothing)
                       (\_ -> Just c)
            `Branch` const f 
    
    lt10 :: FliPprE arg exp => (A arg Int -> E exp r) -> Branch (A arg) (E exp) Int r
    lt10 f = Branch (PartialBij "lt10" (\x -> if x < 10 then Just x else Nothing) Just) f 

    dm10 :: FliPprE arg exp => (A arg Int -> A arg Int -> E exp r) -> Branch (A arg) (E exp) Int r 
    dm10 f = PartialBij "dm10" (\x -> if x < 10 then Nothing else Just (divMod x 10)) (\(d,r) -> Just (10 * d + r))
             `Branch` \z -> unpair z f 


pprExp :: Exp -> Doc
pprExp = pprMode pExp 

parseExp :: [Char] -> Err [Exp]
parseExp =
  G.parse Earley $ parsingModeWith (CommentSpec Nothing (Just (BlockCommentSpec "/*" "*/" False))) pExp 

parseExp' :: [Char] -> Either String [Exp]
parseExp' s = case parseExp s of
                Ok   s -> Right s
                Fail s -> Left (show s) 

exp1 :: Exp
exp1 = Add (Num 1) (Mul (Num 2) (Num 3))

exp2 :: Exp
exp2 = foldr (\x -> if x `mod` 2 == 0 then Mul (Num $ x `div` 2) else Add (Num $ x `div` 2)) (Num 0)
       $ take 100 $ cycle [2..21]

exp3 :: Exp
exp3 = foldl (\r x -> if x `mod` 2 == 0 then Mul r (Num $ x `div` 2) else Add r (Num $ x `div` 2)) (Num 0)
       $ take 100 $ cycle [2..21]


countTime :: String -> IO a -> IO a
countTime str comp = do
  putStrLn $ "Measuring " ++ str ++ "..."
  s <- getCPUTime
  r <- comp
  e <- getCPUTime
  let d = (fromIntegral $ e - s) / (1000000000 :: Double) 
  putStrLn $ "Elapsed: " ++ show d ++ " msec."
  return r 

main :: IO ()
main = do
  countTime "Exp1" $ do 
    putStrLn s1
    print (parseExp' s1)
  countTime "Exp2" $ do 
    putStrLn s2
    print (parseExp' s2)
  countTime "Exp3" $ do 
    putStrLn s3
    print (parseExp' s3)
  where
    s1 = show $ pprExp exp1
    s2 = show $ pprExp exp2
    s3 = show $ pprExp exp3 

