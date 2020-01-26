{-# LANGUAGE LambdaCase, Rank2Types, NamedFieldPuns, TupleSections , MultiWayIf #-}
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
import Coercion ( emptyCvSubstEnv )
import VarEnv ( emptyInScopeSet )
import UniqFM ( UniqFM(..), listToUFM, unitUFM )

import Data.Bitraversable
import Data.Foldable ( foldrM )
import Control.Arrow ( (&&&), (***), first, second )
import Control.Monad ( join )
import Data.Maybe
import Data.Generics hiding ( TyCon, empty )
import Data.Generics.Extra ( everything_ppr, GenericQT(..), gmapQT, mkQT )
import Data.List ( uncons )
import System.Environment ( getArgs )
import Control.Monad.IO.Class ( liftIO )
import Control.Applicative ( Applicative(..), Alternative(..), (<|>) )
import Data.Functor ( ($>) )

import Data.IntMap ( IntMap(..) )
import qualified Data.IntMap as IM
import Data.Map.Strict ( Map(..) )
import qualified Data.Map.Strict as M

import Ra.Lang.Extra ( ppr_unsafe )
import Ra.GHC.Util ( varString, splitFunTysLossy )

import Util
import Lang

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
-- data TyHead = THTyCon TyCon | THTyVar TyVar

instance Ord TyCon where
  a <= b = (U.getKey $ getUnique $ a) <= (U.getKey $ getUnique $ a)
  
instance Ord Class where
  a <= b = (U.getKey $ getUnique $ a) <= (U.getKey $ getUnique $ a)

backsub :: Type -> Type -> Maybe [(Type, Type)] -- require right type to be more specific than left (possibly higher kindedness)
backsub l r | let (lcon, larg) = splitAppTys l
                  (rcon, rarg) = splitAppTys r
                  (rargl, rargr) = splitAt (length rarg - length larg) rarg
            , length larg <= length rarg
            = Just ((lcon, mkAppTys rcon rargl):(zip larg rargr))
backsub _ _ = Nothing



-- max_concrete :: Type -> Type -> Type
-- max_concrete a b = if n_concrete a > n_concrete b then a else b where
--   n_concrete = everything (+) (0 `mkQ` ())

inst_subty :: Type -> Type -> Maybe (Map Id Type)
inst_subty a b =
  let ((fun_tys_a, a'), (fun_tys_b, b')) = both (splitFunTysLossy . everywhere (mkT dropForAlls)) (a, b)
      ((m_app_con_a, m_app_tys_a), (m_app_con_b, m_app_tys_b)) = both (\ty ->
          let (m_con, m_tys) = (fmap fst &&& fmap snd) $ splitAppTy_maybe ty
              m_con_tys' = splitAppTys <$> m_con
          in (fst <$> m_con_tys', liftA2 ((.pure) . (<>) . snd) m_con_tys' m_tys)
        ) (a', b') -- NOTE also splits funtys annoyingly
      
      masum :: [(Type, Type)] -> Maybe (Map Id Type)
      masum = foldrM (flip (fmap . M.union) . uncurry inst_subty) mempty
  in snd ((a, b, a', b', m_app_con_a, m_app_tys_a, m_app_con_b, m_app_tys_b, fun_tys_a, fun_tys_b),
      if | Just bvar <- getTyVar_maybe b -> Just (M.singleton bvar a) -- beta-reduction
         | not $ null fun_tys_a -> -- function type matching
          if length fun_tys_b < length fun_tys_a
            then Nothing -- candidate function doesn't necessarily return function (unless it's `forall`; TODO)
            else
              M.union <$> inst_subty a' (mkFunTys (drop (length fun_tys_a) fun_tys_b) b') -- allow the possibility that the last term of `a` captures a return function from `b`: i.e. `a :: c` matches `b :: d -> e`
              <*> masum (zip fun_tys_a fun_tys_b)
         | Just (tycon_a, tyargs_a) <- splitTyConApp_maybe a -- `a` is a true TyCon
         -> case (m_app_con_b >>= splitTyConApp_maybe) <|> splitTyConApp_maybe b of
          Just (tycon_b, tyargs_b) -- NOTE impossible by no FlexibleInstances
            | tycon_a == tycon_b -> masum $ zip tyargs_a tyargs_b
            | otherwise -> Nothing
          Nothing
            | Just app_con_b <- m_app_con_b
            , Just app_tys_b <- m_app_tys_b
            -> if length tyargs_a >= length app_tys_b
              then
                let (tyargs_a_l, tyargs_a_r) = splitAt (length tyargs_a - length app_tys_b) tyargs_a
                in masum ((mkTyConApp tycon_a tyargs_a_l, app_con_b) : zip tyargs_a_r app_tys_b)
              else Nothing -- kindedness fail
              
            | otherwise -> Nothing -- b isn't tycon, appcon or var... fail or panic?
         | otherwise -> -- `a` is probably a generic AppTy (e.g. `m a`)
            do
              a_args <- m_app_tys_a
              b_args <- m_app_tys_b -- b could be TyConApp in general (although not here by no FlexibleInstances); assume TyConApp is also split by splitAppTys
              let min_kinds =  min (length a_args) (length b_args)
                  (a_args_l, a_args_r) = splitAt (length a_args - min_kinds) a_args
                  (b_args_l, b_args_r) = splitAt (length b_args -min_kinds) b_args
              -- must trim args from the right to match
              conmap <- join $ liftA2 (curry $ uncurry inst_subty . both (uncurry mkAppTys) . ((,a_args_l) *** (,b_args_l))) m_app_con_a m_app_con_b
              argmap <- masum $ zip a_args_r b_args_r
              return $ M.union conmap argmap
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
    
    tl_binds <- (concatMap (bagToList . tm_typechecked_source)) <$> mapM module_tcs (mgModSummaries deps)
    {- everythingBut (<>) (f0 `mkQ` ((\case
                  VarBind _ var rhs _ -> -- somewhere in here is the 
                  _ -> 
                ) :: HsBind GhcTc -> )) -}
    let f0 :: Monoid m => (m, Bool)
        f0 = (mempty, False)
        
        inst_map = everythingBut (M.unionWith (<>)) (f0 `mkQ` ((\case
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
                        (>>= bitraverse tyConClass_maybe ((>>= splitTyConApp_maybe) . one))
                        . splitTyConApp_maybe
                        . dropForAlls
                        . varType
                        . abe_mono
                      ) abs_exports
                    abs_ctx = ev_to_ctx abs_ev_vars
                    cls_map = M.fromListWith (<>) $ map (second (pure . second (pure . (abs_ctx,)))) tyclss
                    cls_inst_map = M.map (M.fromListWith (<>)) cls_map
              , not $ null tyclss
              -> (
                   cls_inst_map -- (\(cls, (tycon, args)) -> ((cls, tycon), [(abs_ev_vars, args)]) )
                  , False
                )
              -- , any (isJust . () . tyConAppTyCon_maybe . dropForAlls . varType . abe_mono) abs_exports 
              -- -> 
            _ -> (mempty, True)
          ) :: HsBind GhcTc -> (ClassInstMap, Bool))) tl_binds
        
        ev_to_ctx :: [EvVar] -> [Constraint]
        ev_to_ctx = catMaybes . map (join . fmap (uncurry (liftA2 (,)) . (tyConClass_maybe *** fmap splitAppTys . one)) . splitTyConApp_maybe . varType)
        
        -- inst_arity = everythingBut (M.unionWith (<>)) (f0 `mkQ` ((\case
        --     VarBind {  }
        --     AbsBinds {} -> (mempty, True)
        --     _ -> 
        --   ) :: HsBind GhcTc -> (Map String Int, Bool)))
        
        find_funs :: [FunCtx] -> GenericQ [Fun]
        find_funs s = (concat . gmapQ (find_funs s))
          `extQ` ((\case
              AbsBinds { abs_tvs, abs_ev_vars, abs_binds } -> find_funs ((abs_tvs, abs_ev_vars):s) abs_binds
              FunBind { fun_id, fun_matches } -> [(s, (unLoc fun_id, fun_matches))]
              _ -> mempty
            ) :: HsBind GhcTc -> [Fun])
        funs = find_funs mempty tl_binds
        
        
        
        -- chk :: Constraint -> Inst -> Maybe [Constraint]
        -- chk
        --   (cn_cls, (cn_var, cn_args))
        --   (inst_cls, (inst_ctx, inst_args))
        --   site -- ask if the ty args of this site of application for this constraint in the signature is compatible with the constraint
        --   | cn_cls == inst_cls -- shove into the map later
        --   , THTyVar cn_tvar <- cn_var
        --   = backsub
        
        tyfind :: TFState -> Maybe [Type]
        tyfind st@(TFState { ctx, sig })
          | Just (cn@(cn_cls, (cn_ty, cn_args)), ctx_rest) <- uncons ctx
          = let cn_tyhead = dropForAlls $ fromMaybe cn_ty $ fmap fst $ splitAppTy_maybe cn_ty -- TODO can we have foralls in constraints? if so, what do they do?
                -- sub_ty is the instance head 
                iter :: Maybe TyVar -> TyCon -> Inst -> Maybe [Type]
                iter m_cn_tyvar tycon (cns', inst_args) =
                  if length inst_args >= length cn_args
                    then
                      let ((inst_argsl, inst_argsr), (cn_argsl, cn_argsr)) = rmatch inst_args cn_args
                          m_sig_subst = flip (TCvSubst emptyInScopeSet) emptyCvSubstEnv
                            . flip unitUFM (mkTyConApp tycon inst_argsl)
                            <$> m_cn_tyvar -- sub protected by arity: still free in fun side
                          m_inst_subst_map = foldr (liftA2 (<>) . uncurry inst_subty) (Just mempty) (zip cn_argsr inst_argsr)
                      in case m_inst_subst_map of
                        Just inst_subst_map ->
                          let inst_subst = TCvSubst emptyInScopeSet (listToUFM $ M.toList $ inst_subst_map) emptyCvSubstEnv
                              subbed_ctx_rest' = map (second (substTy inst_subst *** substTys inst_subst)) ctx_rest
                              subbed_inst_ctx = map (second (substTy inst_subst *** substTys inst_subst)) cns'
                          in tyfind $ TFState {
                            ctx = subbed_ctx_rest' <> subbed_inst_ctx,
                            sig = fromMaybe sig $ flip substTy sig <$> m_sig_subst
                          }
                    else Nothing
          in case getTyVar_maybe cn_tyhead of
              
            -- new tyvar, need to find instances
            Just cn_tyvar -> join $ fmap (mconcat . concatMap (uncurry (map . (uncurry (iter (Just cn_tyvar)) .) . (,))) . M.toList) $ M.lookup cn_cls inst_map
              -- note the mconcat: this is the disjunction
              
            -- [old] tycon, need to verify instances
            Nothing -> case tyConAppTyCon_maybe cn_tyhead of
              Just cn_tycon
                | Just (Just insts) <- M.lookup cn_tycon <$> M.lookup cn_cls inst_map
                -> mconcat $ map (iter Nothing cn_tycon) insts
              Nothing -> Nothing -- or panic?
              
          | otherwise = Just [sig] -- BASE CASE: no more constraints: this passed
    
    -- pure ()
    -- liftIO $ putStrLn $ unlines $ map (uncurry (shim " : ") . (show . U.getKey . getUnique &&& ppr_unsafe) . fst . head . (\(_,_,x) -> x)) inst_map
    liftIO $ putStrLn $ ppr_unsafe $ tyfind (TFState (ev_to_ctx $ snd $ head $ fst $ head funs) (varType $ fst $ snd $ head funs))