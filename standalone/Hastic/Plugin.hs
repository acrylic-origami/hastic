module Hastic.Plugin where

import Hastic
import GhcPlugins ( Plugin(..), impurePlugin, defaultPlugin, CommandLineOption, extractDynFlags )
import GHC.Paths ( libdir )
import GHC
import IOEnv
import Data.IORef
import HscTypes
import TcRnTypes
import Bag ( unionManyBags )

import Control.Arrow ( (&&&), (***), first, second )
import Control.Monad
import System.IO.Unsafe ( unsafePerformIO )
import Control.Monad.IO.Class

import Ra.Lang.Extra ( ppr_unsafe )

plugin :: Plugin
plugin = defaultPlugin {
    typeCheckResultAction = install
    , pluginRecompile = impurePlugin
  }

global_binds :: IORef [LHsBinds GhcTc]
global_binds = unsafePerformIO $ newIORef []

install :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
install opts _ms tc_gbl = do
  env <- getEnv
  let dflags = extractDynFlags env
  binds <- liftIO $ atomicModifyIORef global_binds ((id &&& id) . (tcg_binds tc_gbl :))
  
  when (length binds == (length $ hsc_targets $ env_top env)) $ liftIO $ do
    (analyze $ unionManyBags binds) >>= putStrLn . ppr_unsafe
  
  return tc_gbl