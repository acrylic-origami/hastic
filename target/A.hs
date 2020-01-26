module A where

data A = A

class Foo a where
   
instance Foo A where
  
foo :: Foo a => a -> ()
foo _ = ()