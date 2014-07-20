module Main  where

import Control.Applicative

data Free f a = Pure a | Free (f (Free f a))

instance Functor f => Functor (Free f) where
  fmap f (Pure a)  = Pure (f a)
  fmap f (Free fa) = Free (fmap f <$> fa)
  
instance Functor f => Applicative (Free f) where
  pure = Pure
  Pure a <*> Pure b = Pure $ a b
  Pure a <*> Free mb = Free $ fmap a <$> mb
  Free ma <*> b = Free $ (<*> b) <$> ma

instance Functor f => Monad (Free f) where
  return = Pure
  Pure a >>= f = f a
  Free m >>= f = Free ((>>= f) <$> m)


data Sum a = AddSum Int ( () -> a )
           | TellSum ( Int  -> a )

instance Functor Sum where
  fmap f (AddSum a g) = AddSum a (f. g)
  fmap f (TellSum g) = TellSum (f.g) 

type SumMonad = Free Sum

add x = Free (AddSum x Pure)
tell = Free (TellSum Pure)


test :: SumMonad Int
test = do 
         x <- return 10
         add 25
         y <- tell
         do z <- return 20
            add (z+y)
            tell
         add x    
         tell



main :: IO ()
main = do 
        let a = test
        putStrLn "Hello"
