{-# LANGUAGE LambdaCase, Rank2Types, NamedFieldPuns, TupleSections , MultiWayIf #-}
module Main where

import GHC
import GHC.Paths ( libdir )
import Unique ( Uniquable(..), Unique(..), getUnique )
import qualified Unique as U ( getKey )
import Type
import TyCon
import Var
import Bag ( bagToList, unionManyBags )
import TcEvidence
import ConLike
import Control.Arrow ( (&&&), (***), first, second )
import Outputable ( Outputable, interppSP, showSDocUnsafe, showPpr )
import System.Environment ( getArgs )

import Control.Monad.IO.Class ( liftIO )
import Data.Generics ( Data(..), extQ )
import Data.Generics.Extra ( everything_ppr )
import qualified Data.Map.Strict as M

import Hastic
import Ra.Lang.Extra ( ppr_unsafe )
import Ra.GHC.Util ( varString )

module_tcs :: GhcMonad m => ModSummary -> m TypecheckedModule
module_tcs = (typecheckModule=<<) . parseModule

constr_var_ppr :: Data d => d -> String
constr_var_ppr = everything_ppr (
    (show . toConstr)
    `extQ` (uncurry ((++) . (uncurry ((++) . (++" : ")))) . ((varString &&& uncurry ((++) . (++" :: ")) . (show . varUnique &&& ppr_unsafe . varType)) &&& const "" . constr_var_ppr . varType))
    `extQ` (ppr_unsafe :: TyCon -> String)
    `extQ` (ppr_unsafe :: ConLike -> String)
    `extQ` (ppr_unsafe :: TcEvBinds -> String)
  )
          
main = do
  mod_str:args' <- getArgs
  runGhc (Just libdir) $ do
    dflags <- getSessionDynFlags
    setSessionDynFlags $ dflags {
        importPaths = "target":(importPaths dflags)
      }
    
    target <- guessTarget mod_str Nothing
    setTargets [target] 
    load LoadAllTargets
    deps <- depanal [] False
    
    tl_binds <- unionManyBags . map tm_typechecked_source <$> mapM module_tcs (mgModSummaries deps)
    {- everythingBut (<>) (f0 `mkQ` ((\case
                  VarBind _ var rhs _ -> -- somewhere in here is the 
                  _ -> 
                ) :: HsBind GhcTc -> )) -}
    
          
    -- pure ()
    -- liftIO $ putStrLn $ unlines $ map (uncurry (shim " : ") . (show . U.getKey . getUnique &&& ppr_unsafe) . fst . head . (\(_,_,x) -> x)) inst_map
    -- liftIO $ putStrLn $ ppr_unsafe $ tyfind (TFState (ev_to_ctx $ snd $ head $ fst $ head funs) (varType $ fst $ snd $ head funs))
    liftIO $ do
      let inst_map = find_insts tl_binds
      -- putStrLn $ ppr_unsafe $ map (concretize inst_map) (find_funs tl_binds)
      -- putStrLn $ ppr_unsafe $ varType $ head $ head $ map (uncurry (map . (uncurry setVarType .) . (,))) $ M.toList $ funs
      
      putStrLn $ ppr_unsafe $ analyze_all tl_binds