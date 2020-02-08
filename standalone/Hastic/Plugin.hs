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

global_binds :: IORef [(ClassInstMap, [(Located Id, [Type])])]
global_binds = unsafePerformIO $ newIORef []

install :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
install opts _ms tc_gbl = do
  env <- getEnv
  let dflags = extractDynFlags env
  !binds <- liftIO $ atomicModifyIORef' global_binds ((id &&& id) . ((strictify $ prepare $ tcg_binds tc_gbl) :))
  liftIO $ putStrLn "REV1"
  liftIO $ putStrLn $ show $ length $ snd $ head $ binds
  
  when (length binds == (length $ hsc_targets $ env_top env)) $ liftIO $ do
    putStrLn "ANALYZING!!"
    (uncurry (analyze 4) $ (M.unionsWith (M.unionWith (++)) *** mconcat) $ unzip binds) >>= putStrLn . ppr_unsafe
  
  return tc_gbl