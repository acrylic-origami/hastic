module Hastic.Util where

import Control.Applicative
import Control.Monad.Trans.Maybe ( MaybeT(..) )

-- a is candidate function _to_ substitute, b is function being substituted
-- we want b to be more general than a: the return is a Map of tyvars in b back to things in a

shim :: Monoid m => m -> m -> m -> m
shim b a c = a <> b <> c

liftM :: Monad m => Maybe a -> MaybeT m a
liftM = MaybeT . return -- why doesn't this exist??

one :: [a] -> Maybe a
one [a] = Just a
one _ = Nothing

assoc ((a,b),c) = (a,(b,c))
unassoc (a,(b,c)) = ((a,b),c)

asum :: (Foldable t, Alternative f) => t (f a) -> f a
asum = foldr (<|>) empty

snoc = flip (++) . pure

both f (a, b) = (f a, f b)

rmatch :: [a] -> [b] -> (([a], [a]), ([b], [b]))
rmatch a b =
  let min_len = min (length a) (length b)
  in (splitAt (length a - min_len) a, splitAt (length b - min_len) b)