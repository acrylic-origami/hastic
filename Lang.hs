module Lang where

import Class
import Type
import Var
import Data.Map.Strict ( Map(..) )
import GHC
import Outputable ( Outputable(..), docToSDoc )
import qualified Outputable as O
import qualified Pretty

type Constraint = (Class, (Type, [Type])) -- class name, head, args. Head may be an AppTy or plain with head TyCon or TyVar
type Inst = ([Constraint], [Type]) -- constraints => C ty1 ty2 ...
type InstMap = Map TyCon [Inst]
type ClassInstMap = Map Class InstMap
data TFState = TFState {
    ctx :: [Constraint],
    sig :: Type
  }

str2sdoc = docToSDoc . Pretty.text

instance Outputable TFState where
  ppr (TFState ctx sig) = ((foldr ((O.<>) . (O.<> (str2sdoc "\n")) . ppr) O.empty ctx)) O.<> (str2sdoc "\n**\n") O.<> (ppr sig)
  
  pprPrec r (TFState ctx sig) = ((foldr ((O.<>) . (O.<> (str2sdoc "\n")) . pprPrec r) O.empty ctx)) O.<> (str2sdoc "\n**\n") O.<> (pprPrec r sig)
  
type FunCtx = ([TyVar], [EvVar])
type Fun = ([FunCtx], (Id, MatchGroup GhcTc (LHsExpr GhcTc)))