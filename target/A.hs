module A where

data A = A

class Foo a where
instance Foo () where
instance Foo A where
  
foo = ()