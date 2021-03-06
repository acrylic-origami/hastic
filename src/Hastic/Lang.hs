module Hastic.Lang where

import GHC
import Unique ( Uniquable(..), Unique(..), getUnique )
import qualified Unique as U ( getKey )
import Class
import Type
import Var
import Data.Map.Strict ( Map(..) )
import GHC
import Outputable ( Outputable(..), docToSDoc )
import qualified Outputable as O
import qualified Pretty

-- type Inst = ([TyVar], [EvVar], [(Class, [Type])])
-- data TyHead = THTyCon TyCon | THTyVar TyVar

instance Ord TyCon where
  a <= b = (U.getKey $ getUnique $ a) <= (U.getKey $ getUnique $ a)
  
instance Ord Class where
  a <= b = (U.getKey $ getUnique $ a) <= (U.getKey $ getUnique $ a)
  
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
  ppr (TFState ctx sig) = ((foldr ((O.<>) . (O.<> O.blankLine) . ppr) O.empty ctx)) O.<> (str2sdoc "\n**\n") O.<> (ppr sig)
  
  pprPrec r (TFState ctx sig) = ((foldr ((O.<>) . (O.<> (str2sdoc "\n")) . pprPrec r) O.empty ctx)) O.<> (str2sdoc "\n**\n") O.<> (pprPrec r sig)
  
type Fun = ([Constraint], Located Id)
data BiTree a = BT {
    node :: a,
    child :: [[BiTree a]]
  }

instance Outputable a => Outputable (BiTree a) where
  ppr (BT n ch) = ppr n O.<> O.blankLine O.<> ppr ch
  pprPrec r (BT n ch) = pprPrec r n O.<> O.blankLine O.<> pprPrec r ch

type AppTree = BiTree (Located Id)