module A where

data A a = A a
data B = B

class Foo a where
class Bar a where

instance Bar B where

instance Bar a => Foo (A a) where

foo :: (Bar b, Foo (a b)) => b -> a () -> ()
foo _ _ = ()