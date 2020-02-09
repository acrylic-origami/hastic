{-# LANGUAGE BangPatterns #-}
module Hastic.Plugin where

import Hastic
import Hastic.Lang
import Hastic.Util ( strictify, ppr_unsafe )
import GhcPlugins ( Plugin(..), impurePlugin, defaultPlugin, CommandLineOption, extractDynFlags )
import GHC.Paths ( libdir )
import GHC
import IOEnv
import Data.IORef
import HscTypes
import TcRnTypes
import Bag ( unionManyBags )
import qualified Data.Map.Strict as M

import Control.Arrow ( (&&&), (***), first, second )
import Control.Monad
import System.IO.Unsafe ( unsafePerformIO )
import Control.Monad.IO.Class

plugin :: Plugin
plugin = defaultPlugin {
    typeCheckResultAction = install
    , pluginRecompile = impurePlugin
  }

global_binds :: IORef (Int, (ClassInstMap, [(Located Id, [Type])]))
global_binds = unsafePerformIO $ newIORef (0, (mempty, mempty))

install :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
install opts _ms tc_gbl = do
  env <- getEnv
  let dflags = extractDynFlags env
  !(num_modules, !binds) <- liftIO $ atomicModifyIORef' global_binds (\(num_modules', (instmap, fns)) ->
        let (instmap', fns') = strictify $ prepare 4 $ tcg_binds tc_gbl
            ret = (num_modules' + 1, (M.unionWith (M.unionWith (++)) instmap instmap', fns <> fns'))
        in (ret, ret)
      )
  liftIO $ putStrLn "REV4"
  
  when (num_modules == (length $ hsc_targets $ env_top env)) $ liftIO $ do
    putStrLn ("Analyzing: " ++ (show $ length $ snd binds) ++ " functions, " ++ (show $ M.foldr' ((+) . M.foldr' ((+) . length) 0) 0 $ fst binds) ++ " instances")
    () <$ uncurry (analyze 4) binds
  
  return tc_gbl