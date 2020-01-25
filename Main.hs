{-# LANGUAGE LambdaCase, Rank2Types, NamedFieldPuns, TupleSections #-}
module Main where

import GHC
import GHC.Paths ( libdir )
import Unique ( Uniquable(..), Unique(..), getUnique )
import qualified Unique as U ( getKey )
import Type
import TyCon
import Var
import Bag
import TcEvidence
import Outputable ( Outputable, interppSP, showSDocUnsafe, showPpr )
import Class ( Class(..) )
import ConLike ( ConLike(..) )

import Data.Bitraversable
import Control.Arrow ( (&&&), (***), first, second )
import Data.Maybe
import Data.Generics hiding ( TyCon, empty )
import Data.Generics.Extra ( everything_ppr )
import System.Environment ( getArgs )
import Control.Monad.IO.Class ( liftIO )
import Control.Applicative ( Applicative(..), Alternative(..), (<|>) )
import Data.Functor ( ($>) )

import Data.IntMap ( IntMap(..) )
import qualified Data.IntMap as IM
import Data.Map.Strict ( Map(..) )
import qualified Data.Map.Strict as M
import Deque.Lazy ( Deque(..), snoc, uncons ) -- queue operation

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

-- type Inst = ([TyVar], [EvVar], [(Class, [Type])])
type Inst = (Class, ([EvVar], [Type])) -- constraints => C ty1 ty2 ...
type InstMap = Map TyCon [Inst]
type Constraint = (Class, (TyVar, [Type])) -- 
data TFState = TFState {
    ctx :: Deque Constraint,
    objs :: Map Var [TyCon]
  }
type FunCtx = ([TyVar], [EvVar])
type Fun = ([FunCtx], (Id, MatchGroup GhcTc (LHsExpr GhcTc)))

shim :: Monoid m => m -> m -> m -> m
shim b a c = a <> b <> c

one :: [a] -> Maybe a
one [a] = Just a
one _ = Nothing

assoc ((a,b),c) = (a,(b,c))
unassoc (a,(b,c)) = ((a,b),c)

asum :: (Foldable t, Alternative f) => t (f a) -> f a
asum = foldr (<|>) empty

instance Ord TyCon where
  a <= b = (U.getKey $ getUnique $ a) <= (U.getKey $ getUnique $ a)
  
instance Ord Class where
  a <= b = (U.getKey $ getUnique $ a) <= (U.getKey $ getUnique $ a)

backsub :: Type -> Type -> Maybe [(Type, Type)]
backsub l r | let (lcon, largs) = splitAppTys l
                  (rcon, rargs) = splitAppTys r
            , length largs == length rargs
            = Just ((lcon, rcon):(zip largs rargs))
backsub _ _ = Nothing

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
    
    tl_binds <- (concatMap (bagToList . tm_typechecked_source)) <$> mapM module_tcs (mgModSummaries deps)
    {- everythingBut (<>) (f0 `mkQ` ((\case
                  VarBind _ var rhs _ -> -- somewhere in here is the 
                  _ -> 
                ) :: HsBind GhcTc -> )) -}
    let f0 :: Monoid m => (m, Bool)
        f0 = (mempty, False)
        
        insts = everythingBut (M.unionWith (<>)) (f0 `mkQ` ((\case
            AbsBinds { abs_tvs, abs_ev_vars, abs_exports }
              | let tyclss :: [(Class, (TyCon, [Type]))]
                    tyclss = catMaybes $ map (
                        -- (>>= (second splitTyConApp_maybe . one)) -- assert not a MultiParamTypeClass
                        -- . (>>= (
                        --     uncurry fmap . (
                        --         flip first
                        --         &&& fmap const . tyConClass_maybe . fst
                        --       )
                        --   ))
                        (>>= bitraverse tyConClass_maybe ((>>=splitTyConApp_maybe) . one))
                        . splitTyConApp_maybe
                        . dropForAlls
                        . varType
                        . abe_mono
                      ) abs_exports
              , not $ null tyclss
              -> (
                  M.fromListWith (<>) $ map (\(cls, (tycon, args)) -> 
                      (tycon, [(cls, (abs_ev_vars, args))])
                    ) tyclss
                  , False
                )
              -- , any (isJust . () . tyConAppTyCon_maybe . dropForAlls . varType . abe_mono) abs_exports 
              -- -> 
            _ -> (mempty, True)
          ) :: HsBind GhcTc -> (InstMap, Bool))) tl_binds
        
        -- inst_map :: InstMap
        -- inst_map = foldr (\(_tv, ev, cls_tys) ->
        --     M.unionWith (<>) (foldr (
        --         uncurry (M.insertWith (<>)) . second (map (ev,))
        --       ) M.empty cls_tys)
        --   ) M.empty insts -- flip the class payload inside-out
        
        find_funs :: [FunCtx] -> GenericQ [Fun]
        find_funs s = (concat . gmapQ (find_funs s))
          `extQ` ((\case
              AbsBinds { abs_tvs, abs_ev_vars, abs_binds } -> find_funs ((abs_tvs, abs_ev_vars):s) abs_binds
              FunBind { fun_id, fun_matches } -> [(s, (unLoc fun_id, fun_matches))]
              _ -> mempty
            ) :: HsBind GhcTc -> [Fun])
        funs = find_funs mempty tl_binds
        
        chk :: Constraint -> Inst -> Maybe [Constraint]
        chk
          (cn_cls, (cn_var, cn_args))
          (inst_cls, (inst_ctx, inst_args))
          = undefined
        
        tyfind :: TFState -> Map Var [Type]
        tyfind st@(TFState { ctx, objs })
          | Just (cn@(cn_cls, (cn_var, cn_args)), ctx_rest) <- uncons ctx
          , null objs || not (any null objs)
          = tyfind $ case M.lookup cn_var objs of
            Just objs' ->
              let m_new_ctx :: [Maybe [Constraint]]
                  m_new_ctx = map (
                      (>>= (asum . map (chk cn)))
                      . flip M.lookup insts
                    ) objs'  -- for each 
              in st {
                ctx = foldr snoc ctx (concat $ catMaybes m_new_ctx),
                objs = M.adjust (catMaybes . map (uncurry ($>)) . zip m_new_ctx) cn_var objs -- Constraint -> [TyCon] -> [TyCon]
              }
            Nothing ->
              let m_new_ctx :: [(TyCon, Maybe [Constraint])]
                  m_new_ctx = map (second (asum . map (chk cn))) $ M.toList insts
                  next_insts = catMaybes $ map (uncurry (<$)) m_new_ctx
              in st {
                ctx = foldr snoc ctx (concat $ catMaybes $ map snd m_new_ctx),
                objs = M.insert cn_var next_insts objs
              }
          | otherwise = M.map (map mkTyConTy) objs -- M.map (map (snd . snd)) objs
    
    pure ()
    -- liftIO $ putStrLn $ unlines $ map (uncurry (shim " : ") . (show . U.getKey . getUnique &&& ppr_unsafe) . fst . head . (\(_,_,x) -> x)) insts