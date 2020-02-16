{-# LANGUAGE Rank2Types #-}
module Hastic.Util where

import Outputable ( Outputable(..), showPpr, interppSP, showSDocUnsafe )
import Var ( varName, varType, varUnique )
import Name ( nameOccName )
import OccName ( occNameString )

import Data.Foldable ( foldl' )
import Control.Applicative
import Control.Monad.Trans.Maybe ( MaybeT(..) )

import Data.Functor.Identity
import Data.Generics ( Data(..), GenericT, extQ )
import Data.Generics.Extra ( everything_ppr )

import Control.Arrow ( (&&&), (***), first, second )
import TyCon ( TyCon(..) )
import ConLike ( ConLike(..) )
import TcEvidence

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

-- strict concat

concat' :: Foldable t => t [a] -> [a]
concat' = foldl' (++) []

concatMap' :: Foldable t => (a -> [b]) -> t a -> [b]
concatMap' f = foldl' ((.f) . (++)) []

rmatch :: [a] -> [b] -> (([a], [a]), ([b], [b]))
rmatch a b =
  let min_len = min (length a) (length b)
  in (splitAt (length a - min_len) a, splitAt (length b - min_len) b)

-- strict transformer
gmapT' :: GenericT -> GenericT
gmapT' f x0 = runIdentity (gfoldl k Identity x0)
  where
    k :: Data d => Identity (d->b) -> d -> Identity b
    k (Identity c) x = Identity $! c $! f x -- let the user control strictness in `f`

strictify :: GenericT
strictify = gmapT' strictify

ppr_unsafe :: Outputable a => a -> String
ppr_unsafe = showSDocUnsafe . interppSP . pure

varString = occNameString . nameOccName . varName

constr_var_ppr :: Data d => d -> String
constr_var_ppr = everything_ppr (
    (show . toConstr)
    `extQ` (uncurry ((++) . (uncurry ((++) . (++" : ")))) . ((varString &&& uncurry ((++) . (++" :: ")) . (show . varUnique &&& ppr_unsafe . varType)) &&& const "" . constr_var_ppr . varType))
    `extQ` (ppr_unsafe :: TyCon -> String)
    `extQ` (ppr_unsafe :: ConLike -> String)
    `extQ` (ppr_unsafe :: TcEvBinds -> String)
  )