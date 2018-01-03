module Text.FliPpr.Err where

import Text.FliPpr.Doc as D 

data Err a = Ok a | Fail D.Doc

instance Functor Err where
  fmap f (Ok a)   = Ok (f a)
  fmap _ (Fail d) = Fail d

instance Applicative Err where
  pure = return
  Fail d <*> Ok _    = Fail d
  Fail d <*> Fail d' = Fail (d D.$$ d')
  Ok   _ <*> Fail d  = Fail d
  Ok   f <*> Ok a    = Ok (f a)

instance Monad Err where
  return = Ok
  Fail d >>= _ = Fail d
  Ok a >>= f   = f a 

  fail = Fail . D.text 

instance Show a => Show (Err a) where
  show (Ok a)   = "Ok " ++ show a
  show (Fail s) = show (D.text "Error: " <+> D.align s)

err :: D.Doc -> Err a 
err = Fail 
