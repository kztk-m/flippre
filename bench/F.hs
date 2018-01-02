{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecursiveDo #-}

import Text.FliPpr
import Text.FliPpr.Doc

import qualified Text.FliPpr.Internal.GrammarST as G 

example1 :: FliPpr ([Bool] :~> D)
example1 = flippr $ do
  let manyParens d = local $ do
        rec m <- share $ d <? parens m
        return m

  pprTF <- share $ arg $ \i -> manyParens $ case_ i
    [ unTrue  `Branch` \_ -> text "True",
      unFalse `Branch` \_ -> text "False" ]

  rec ppr <- share $ arg $ \x -> manyParens $ case_ x
              [ unNil  `Branch` \_ -> text "[" <> text "]",
                unCons `Branch` \xx -> unpair xx $ \a x -> 
                  brackets (ppr' `app` a `app` x)]

      ppr' <- share $ arg $ \a -> arg $ \x -> case_ x
        [ unNil `Branch` \_ -> pprTF `app` a, 
          unCons `Branch` \xx -> 
                  unpair xx $ \b x -> 
                     pprTF `app` a <> text "," <+>. ppr' `app` b `app` x]
  return ppr
  where
    unTrue  = PInv "unTrue" (\x -> if x then Just () else Nothing) (const (Just True))
    unFalse = PInv "unFalse" (\x -> if x then Nothing else Just ()) (const (Just False))

    unNil = PInv "unNil" f g
      where
        f [] = Just ()
        f _  = Nothing
        g () = Just []
    unCons = PInv "unCons" f g
      where
        f [] = Nothing
        f (a:x) = Just (a,x)
        g (a,x) = Just (a:x) 
    
main :: IO ()
main = do
  let g = parsingMode example1
  print $ g
  putStrLn "------------------------------"
  print $ G.inline $ G.removeNonProductive $ G.optSpaces g
