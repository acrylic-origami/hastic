{-# LANGUAGE LambdaCase, Rank2Types, NamedFieldPuns, TupleSections , MultiWayIf #-}
module Hastic (
  analyze_all,
  find_insts,
  find_funs,
  unify,
  apptree_ast
) where

import GHC
import Type
import TyCon
import Var
import Bag
import TcEvidence
import Unique ( Uniquable(..), Unique(..), getUnique )
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
import Data.Generics.Extra ( GenericQT(..), gmapQT, mkQT )
import Data.List ( uncons, subsequences )
import System.Environment ( getArgs )
import Control.Applicative ( Applicative(..), Alternative(..), (<|>) )
import Data.Functor ( ($>) )

import Data.IntMap ( IntMap(..) )
import qualified Data.IntMap as IM
import Data.Map.Strict ( Map(..) )
import qualified Data.Map.Strict as M

import Ra.Lang.Extra ( ppr_unsafe )
import Ra.GHC.Util ( splitFunTysLossy )

import Hastic.Util
import Hastic.Lang

apptree_ast :: AppTree -> [LHsExpr GhcTc]
apptree_ast (BT n ch) = apptree_ast' (noLoc (HsVar NoExt (noLoc n))) ch where
  apptree_ast' term (arg:rest) = concatMap (concatMap (flip apptree_ast' rest . noLoc . HsApp NoExt term) . apptree_ast) arg
  apptree_ast' term [] = [term]

map2subst :: Map Id Type -> TCvSubst
map2subst m = TCvSubst emptyInScopeSet (listToUFM $ M.toList m) emptyCvSubstEnv

ev_to_ctx :: [EvVar] -> [Constraint]
ev_to_ctx = catMaybes . map (join . fmap (uncurry (liftA2 (,)) . (tyConClass_maybe *** fmap splitAppTys . one)) . splitTyConApp_maybe . varType)

-- max_concrete :: Type -> Type -> Type
-- max_concrete a b = if n_concrete a > n_concrete b then a else b where
--   n_concrete = everything (+) (0 `mkQ` ())

unify :: Type -> Type -> Maybe (Map Id Type, Map Id Type)
unify x y = liftA2 (,) (unify' y x) (unify' x y) where -- sorry for flipped args, felt like it made sense to make the first arg the concrete one first
  unify' a b = -- only bind `b` to more specific aspects of `a`
    let ((app_con_a, app_args_a), (app_con_b, app_args_b)) = both splitAppTys (a, b) -- NOTE also splits funtys annoyingly
        masum :: [(Type, Type)] -> Maybe (Map Id Type)
        masum = foldrM (flip (fmap . M.union) . uncurry unify') mempty
    in if | null app_args_b
          , Just bvar <- getTyVar_maybe b -> Just (M.singleton bvar a) -- `b` is totally free (or something else unexpected)
          | Just (tycon_a, tyargs_a) <- splitTyConApp_maybe a -- `a` is a true TyCon
          -> case splitTyConApp_maybe app_con_b of
            Just (tycon_b, tyargs_b) -- `b` is also a true TyCon
              | tycon_a == tycon_b -> masum $ zip tyargs_a tyargs_b
              | otherwise -> Nothing
            Nothing
              | length tyargs_a >= length app_args_b
              -> let (tyargs_a_l, tyargs_a_r) = splitAt (length tyargs_a - length app_args_b) tyargs_a
                 in masum ((mkTyConApp tycon_a tyargs_a_l, app_con_b) : zip tyargs_a_r app_args_b)
              | otherwise -> Nothing -- kindedness fail
          | not (null app_args_a)
          -> let ((args_al, args_ar), (args_bl, args_br)) = rmatch app_args_a app_args_b
             in foldr (liftA2 (<>) . uncurry unify') (Just mempty) (zip (mkAppTys app_con_a args_al : args_ar) (mkAppTys app_con_b args_bl : args_br))
          | otherwise -> Just mempty

find_insts :: LHsBinds GhcTc -> ClassInstMap
find_insts = everythingBut (M.unionWith (<>)) (
    (mempty, False) `mkQ` ((\case
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
      ) :: HsBind GhcTc -> (ClassInstMap, Bool))
  )

find_funs :: LHsBinds GhcTc -> [Fun]
find_funs = find_funs' mempty where
  find_funs' :: [Constraint] -> GenericQ [Fun]
  find_funs' s = (concat . gmapQ (find_funs' s))
    `extQ` ((\case
        AbsBinds { abs_tvs, abs_ev_vars, abs_binds } -> find_funs' (ev_to_ctx abs_ev_vars ++ s) abs_binds
        FunBind { fun_id, fun_matches } -> [(s, unLoc fun_id)]
        _ -> mempty
      ) :: HsBind GhcTc -> [Fun])

concretize :: ClassInstMap -> Fun -> Maybe (Id, [Type])
concretize inst_map raw_fun = fmap (snd raw_fun,) $ uncurry ((tyfind .) . TFState) $ second varType raw_fun where
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
                    m_inst_subst_map = fmap snd $ foldr (liftA2 (<>) . uncurry unify) (Just mempty) (zip cn_argsr inst_argsr)
                in case m_inst_subst_map of
                  Just inst_subst_map ->
                    let inst_subst = map2subst inst_subst_map
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

analyze_all :: LHsBinds GhcTc -> [LHsExpr GhcTc]
analyze_all binds =
  let inst_map = find_insts binds
      raw_funs = find_funs binds
      
      -- funs :: Map Id [Type]
      funs = M.fromList $ catMaybes $ map (concretize inst_map) raw_funs
      
      expand_fun :: Int -> Id -> Maybe AppTree
      expand_fun n _ | n <= 0 = Nothing
      expand_fun n f0 =
        let (f0_args, f0_ret) = splitFunTys (varType f0)
        
            go :: [Type] -> Maybe [[AppTree]]
            go [] = Just mempty
            go (arg0:argrest) =
              foldr (\a b ->
                  (liftA2 ((map (uncurry (<>)) .) . zip) a b) <|> a <|> b -- disjunction
                ) Nothing -- transpose of sorts, squeeze outer list (of alternatives) into innermost list (of alternatives) per arg: all arg lengths equal by design
              -- disjunction, but not mconcat because it cats the wrong list dimension
              $ concatMap (\(fn_var, fn_tys) -> -- [Maybe [[BiTree Id]]]: alts-args-alts
                concatMap (\fn_ty ->
                    let (fn_args, fn_ret) = splitFunTys fn_ty
                    in [
                        do
                          (arg0_mapper, fn_mapper) <- unify arg0 fn_ret
                          this_exprs <- expand_fun (n - 1) (setVarType fn_var $ substTy (map2subst fn_mapper) (mkFunTys fn_args' (mkFunTys fn_ret_args fn_ret)))
                          next_exprs <- go (substTys (map2subst arg0_mapper) argrest)
                          return ([this_exprs] : next_exprs) -- why is this list wrapped? it's a bit odd... maybe awaiting concat at the outer level
                        | (fn_args', fn_ret_args) <- zip (reverse (subsequences fn_args)) (map reverse $ subsequences (reverse fn_args))
                      ]
                  ) fn_tys
              ) $ M.toList funs
        in BT f0 <$> go f0_args
      
      
  in concat $ catMaybes $ map (fmap apptree_ast . expand_fun 10) $ concatMap (uncurry (map . (uncurry setVarType .) . (,))) $ M.toList $ funs