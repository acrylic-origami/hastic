{-# LANGUAGE LambdaCase, Rank2Types, NamedFieldPuns, TupleSections , MultiWayIf, BangPatterns #-}
module Main where

import GHC
import GHC.Paths ( libdir )
import DynFlags
import Unique ( Uniquable(..), Unique(..), getUnique )
import qualified Unique as U ( getKey )
import Type
import TyCon
import Var
import FastString ( fsLit )
import Name ( mkSystemVarName, nameUnique )
import Bag ( bagToList, unionManyBags )
import TcEvidence
import ConLike
import Control.Arrow ( (&&&), (***), first, second )
import Outputable ( Outputable, interppSP, showSDocUnsafe, showPpr )
import System.Environment ( getArgs )

import Control.Monad.IO.Class ( liftIO )
import Control.Monad.Random ( evalRand )
import System.Random ( getStdGen, StdGen )
import Data.Generics ( Data(..), extQ, everywhere, mkT )
import qualified Data.Map.Strict as M

import Hastic
import Hastic.Util ( strictify, ppr_unsafe, varString, constr_var_ppr )

module_tcs :: GhcMonad m => ModSummary -> m TypecheckedModule
module_tcs = (typecheckModule=<<) . parseModule

pkgs = ["ghc", "ghc-paths", "ghc-prim", "integer-gmp"]

main = do
  mod_str:depth':n':args' <- getArgs
  let depth :: Int
      depth = read depth'
      n :: Int
      n = read n'
  runGhc (Just libdir) $ do
    dflags <- getSessionDynFlags
    setSessionDynFlags $ dflags {
        importPaths = "target":"purebase.old/base":"purebase.old/hiddens":(importPaths dflags),
        packageFlags = packageFlags dflags ++ map (\pkg -> ExposePackage pkg (PackageArg pkg) (ModRenaming True []) ) pkgs
      }
    
    liftIO $ putStrLn "Typechecking..."
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
      putStrLn "Preparing..."
      let inst_map = find_insts tl_binds
          !prep = strictify $ prepare depth tl_binds
          !ph = foldl1 const [0..1000000]
      -- putStrLn $ ppr_unsafe $ map (concretize inst_map) (find_funs tl_binds)
      -- putStrLn $ ppr_unsafe $ varType $ head $ head $ map (uncurry (map . (uncurry setVarType .) . (,))) $ M.toList $ funs
      -- putStrLn $ show $ length $ snd prep
      -- return ()
      putStrLn ("Analyzing: " ++ (show $ length $ snd prep) ++ " functions, " ++ (show $ M.foldr' ((+) . M.foldr' ((+) . length) 0) 0 $ fst prep) ++ " instances")
      -- putStrLn $ unlines $ map (ppr_unsafe . fst) (snd prep)
      -- gen <- getStdGen
      -- putStrLn $ "GEN: " ++ show gen
      let gen :: StdGen
          gen = read "53971238 1"
      putStrLn $ ppr_unsafe $ everywhere (mkT (\v -> setVarName v $ mkSystemVarName (nameUnique $ varName v) (fsLit (ppr_unsafe v ++ " :: " ++ ppr_unsafe (varType v))))) $ (!!n) $ (`evalRand` gen) $ (!!1) $ uncurry (analyze depth) prep
      
      -- everywhere (mkT (\v -> setVarName v $ mkSystemVarName (nameUnique $ varName v) (fsLit (ppr_unsafe v ++ " :: " ++ ppr_unsafe (varType v)))))