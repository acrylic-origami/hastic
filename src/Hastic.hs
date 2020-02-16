{-# LANGUAGE LambdaCase, Rank2Types, NamedFieldPuns, TupleSections , MultiWayIf, BangPatterns #-}
module Hastic (
  analyze,
  find_insts,
  find_funs,
  concretize,
  unify,
  apptree_ast,
  prepare
) where

import GHC
import Type
import TyCon
import Var
import FastString ( fsLit )
import Bag
import TcEvidence
import Unique ( Uniquable(..), Unique(..), getUnique, mkCoVarUnique )
import Name ( mkSystemName )
import OccName ( mkVarOcc )
import Class ( Class(..) )
import ConLike ( ConLike(..) )
import Coercion ( emptyCvSubstEnv )
import VarEnv ( emptyInScopeSet )
import UniqFM ( UniqFM(..), listToUFM, unitUFM )

import System.Environment ( getArgs )
import Control.Monad.Random.Class ( MonadRandom(..) )
import Control.Monad.Random ( Rand(..) )
import System.Random ( StdGen(..) )

import Data.Bitraversable
import Data.Foldable ( foldrM )
import Control.Arrow ( (&&&), (***), first, second )
import Control.Monad ( join )
import Control.Monad.Trans ( MonadTrans(..) )
import Control.Monad.Trans.Maybe ( MaybeT(..) )
import Control.Monad.State.Lazy ( StateT(..) )
import Data.Semigroup ( mtimesDefault )
import Data.Maybe
import Data.Generics hiding ( TyCon, empty )
import Data.Generics.Extra ( GenericQT(..), gmapQT, mkQT )
import Data.List ( uncons, subsequences )
import Control.Applicative ( Applicative(..), Alternative(..), (<|>) )
import Data.Functor ( ($>) )

import Data.IntMap ( IntMap(..) )
import qualified Data.IntMap as IM
import Data.Map.Lazy ( Map(..) )
import qualified Data.Map.Lazy as M
import qualified Data.Map.Merge.Lazy as MMerge

import Hastic.Util
import Hastic.Lang

import Debug.Trace ( trace )

-- trace x y = y

apptree_ast :: AppTree -> [LHsExpr GhcTc]
apptree_ast (BT n ch) = apptree_ast' (noLoc (HsVar NoExt n)) ch where
  apptree_ast' term (arg:rest) = concatMap (concatMap (flip apptree_ast' rest . noLoc . HsPar NoExt . noLoc . HsApp NoExt term) . apptree_ast) arg
  apptree_ast' term [] = [term]

map2subst :: Map Id Type -> TCvSubst
map2subst m = TCvSubst emptyInScopeSet (listToUFM $ M.toList m) emptyCvSubstEnv

ev_to_ctx :: [EvVar] -> [Constraint]
ev_to_ctx = catMaybes . map (join . fmap (uncurry (liftA2 (,)) . (tyConClass_maybe *** fmap (splitAppTys . dropForAlls) . one)) . splitTyConApp_maybe . varType) -- the `one` assumes single-param classes: i.e. class tycon application has one argument: other classes are ignored

-- max_concrete :: Type -> Type -> Type
-- max_concrete a b = if n_concrete a > n_concrete b then a else b where
--   n_concrete = everything (+) (0 `mkQ` ())

-- type UnifyST = StateT (Bimap (Maybe Id) (Maybe Id)) Identity 
unify :: Type -> Type -> Maybe (Map Id Type)
unify x y | Nothing <- getRuntimeRep_maybe x = Nothing
unify x y | Nothing <- getRuntimeRep_maybe y = Nothing
unify x y = unify' 16 y x where -- sorry for flipped args, felt like it made sense to make the first arg the concrete one
  unify' :: Int -> Type -> Type -> Maybe (Map Id Type)
  unify' 0 a b = error ("Unification failure: " ++ (ppr_unsafe a) ++ " <> " ++ (ppr_unsafe b))
  unify' n a b = -- only bind `b` to more specific aspects of `a`
    let ((app_con_a, app_args_a), (app_con_b, app_args_b)) = both (\ty ->
            if | Just (arg0, ret0) <- splitFunTy_maybe ty
               -> [arg0, ret0] <$ splitAppTys ty
               | otherwise -> splitAppTys ty 
          ) (a, b) -- NOTE also splits funtys annoyingly
        ((fa_tyvars_a, fa_ty_a), (fa_tyvars_b, fa_ty_b)) = both splitForAllTys (a, b)
        merger :: Map Id Type -> Map Id Type -> Maybe (Map Id Type)
        merger a b =
          (M.foldrWithKey (liftA2 . M.insert) (Just mempty)) -- Map (Maybe a) -> Maybe (Map a)
          $ MMerge.merge
              (MMerge.mapMissing (flip (const . Just)))
              (MMerge.mapMissing (flip (const . Just)))
              (MMerge.zipWithMatched (\_ x y -> if x `eqType` y then Just x else Nothing))
              a b
        masum :: [(Type, Type)] -> Maybe (Map Id Type)
        masum = foldr ((join.)
            . liftA2 merger
            . uncurry (unify' (n - 1))
          )
          (Just mempty)
    in if 
       -- FORALLS
       | (not (null fa_tyvars_a) || not (null fa_tyvars_b))
       -> foldr (\ty m -> liftA2 const m $ isTyVarTy <$> (M.lookup ty =<< m)) (unify' n fa_ty_a fa_ty_b) fa_tyvars_b
              
       -- `b` FREE
       | null app_args_b
       , Just bvar <- getTyVar_maybe b
       -> Just (M.singleton bvar a) -- `b` is totally free (or something else unexpected)
       
       -- `a` TYCON
       | Just (tycon_a, _) <- splitTyConApp_maybe app_con_a -- `a` is a true TyCon
       -> case splitTyConApp_maybe app_con_b of -- trace (ppr_unsafe (tycon_a, app_args_a, b, app_args_b)) $ 
        Just (tycon_b, _) -- `b` is also a true TyCon
          | tycon_a == tycon_b
          -> masum $ zip app_args_a app_args_b
          | otherwise -> Nothing
        Nothing
          | length app_args_a >= length app_args_b
          -> let (app_args_a_l, app_args_a_r) = splitAt (length app_args_a - length app_args_b) app_args_a
             in masum ((mkTyConApp tycon_a app_args_a_l, app_con_b) : zip app_args_a_r app_args_b)
          | otherwise -> Nothing -- kindedness fail (a -> b)
       
       -- `a` APPCON
       | length app_args_b < length app_args_a
       -> Nothing -- kindedness fail (b -> a)
       | not (null app_args_a)
       -> let ((args_al, args_ar), (args_bl, args_br)) = rmatch app_args_a app_args_b
          in masum (zip (mkAppTys app_con_a args_al : args_ar) (mkAppTys app_con_b args_bl : args_br))
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
                    . uncurry (>>)
                    . (getRuntimeRep_maybe &&& splitTyConApp_maybe)
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
        FunBind { fun_id, fun_matches } -> [(s, fun_id)]
        _ -> mempty
      ) :: HsBind GhcTc -> [Fun])

concretize :: Int -> ClassInstMap -> Fun -> Maybe (Located Id, [Type])
concretize depth inst_map raw_fun = fmap (snd raw_fun,) $ uncurry ((tyfind (max 1 (depth * length (fst raw_fun))) .) . TFState) $ second (varType . unLoc) raw_fun where
  tyfind :: Int -> TFState -> Maybe [Type]
  tyfind 0 _ = Nothing
  tyfind n st@(TFState { ctx, sig })
    | Just (cn@(cn_cls, (cn_tyhead, cn_args)), ctx_rest) <- uncons ctx
    = let -- closes over cn_args, cn_tyhead
          iter :: TyCon -> Inst -> Maybe [Type]
          iter inst_tycon (cns', inst_args) =
            if length inst_args >= length cn_args
              then
                let ((inst_argsl, inst_argsr), (cn_argsl, cn_argsr)) = rmatch inst_args cn_args
                    m_sig_subst = flip (TCvSubst emptyInScopeSet) emptyCvSubstEnv
                      . flip unitUFM (mkTyConApp inst_tycon inst_argsl)
                      <$> (getTyVar_maybe cn_tyhead) -- sub protected by arity: still free in fun side
                    m_inst_subst_map = foldr (liftA2 (<>) . uncurry unify) (Just mempty) (zip cn_argsr inst_argsr)
                in case m_inst_subst_map of
                  Just inst_subst_map ->
                    let inst_subst = map2subst inst_subst_map
                        subbed_ctx_rest' = map (second (substTy inst_subst *** substTys inst_subst)) ctx_rest
                        subbed_inst_ctx = map (second (substTy inst_subst *** substTys inst_subst)) cns'
                    in tyfind (n - 1) $ TFState {
                      ctx = subbed_ctx_rest' <> subbed_inst_ctx,
                      sig = fromMaybe sig $ flip substTy sig <$> m_sig_subst
                    }
                  Nothing -> Nothing
              else Nothing
    in case getTyVar_maybe cn_tyhead of
        
      -- new tyvar, need to find instances
      Just cn_tyvar ->
        join
        $ fmap (
            mconcat
            . concatMap (
                uncurry (map . (uncurry iter .) . (,)) -- map original fun id into the inner tuple of possible concrete types
              )
            . M.toList
          )
        $ M.lookup cn_cls inst_map
        -- note the mconcat: this is the disjunction
        
      -- [old] tycon, need to verify instances
      Nothing -> case tyConAppTyCon_maybe cn_tyhead of
        Just inst_tycon
          | Just (Just insts) <- M.lookup inst_tycon <$> M.lookup cn_cls inst_map
          -> mconcat $ map (iter inst_tycon) insts
        Nothing -> Nothing -- or panic?
        
    | otherwise = Just [sig] -- BASE CASE: no more constraints: this passed

bot_var :: Located Id
bot_var = noLoc $ mkCoVar (mkSystemName (mkCoVarUnique 0) (mkVarOcc "_|_")) (mkStrLitTy (fsLit "_|_"))

prepare :: Int -> LHsBinds GhcTc -> (ClassInstMap, [(Located Id, [Type])])
prepare depth binds =
  let inst_map = find_insts binds
  in (inst_map, catMaybes $ map (concretize depth inst_map) $ find_funs binds)

fRAC = 1

mk_app :: LHsExpr GhcTc -> [LHsExpr GhcTc] -> LHsExpr GhcTc
mk_app con [] = con
mk_app con exprs = foldl ((noLoc.) . HsApp NoExt) con exprs

analyze :: Int -> ClassInstMap -> [(Located Id, [Type])] -> [Rand StdGen [LHsExpr GhcTc]] -- one for each function alt
analyze depth inst_map funs = 
  let funs' = IM.fromList $ zip [0..] funs
      expand_fun :: Int -> Located Id -> Rand StdGen [LHsExpr GhcTc]
      expand_fun 0 _ = return [noLoc (HsVar NoExt bot_var)]
      expand_fun n f0 =
        -- trace (ppr_unsafe f0) $
        let (f0_args, _f0_ret) = splitFunTys (varType $ unLoc f0)
            n_target_funs = floor (fRAC * (fromIntegral $ IM.size funs'))
            target_funs :: [Rand StdGen (Located Id, [Type])]
            target_funs = map (fmap (funs' IM.!)) $ replicate n_target_funs (getRandomR (0, IM.size funs' - 1))
            f0_expr = (HsVar NoExt . noLoc) <$> f0
            go :: Int -> [Type] -> [Rand StdGen [[LHsExpr GhcTc]]] -- alt-arg
            go _ [] = [return [[]]]
            go 0 args = [return [map (const (noLoc (HsVar NoExt bot_var))) args]]
            go n' (arg0:argrest) =
              -- trace (show n') $
              map (\m_fn -> do -- Rand [[LHsExpr]]: alts-args
                  -- NGL this treatment of the monad sequencing is a bit of a guess, but I think this'll still be lazy to pull up the first result quickly
                  (fn_var, fn_tys) <- m_fn
                  -- alternatives over function synthesized type definitions
                  -- in particular, sequence here is a bit questionable, but I think it's still right wrt a fast first result
                  fmap concat $ sequence $ concatMap (\fn_ty ->
                      -- trace ("FN_TY_ALTS " ++ ppr_unsafe fn_ty) $
                      let (fn_args, fn_ret) = splitFunTys $ dropForAlls fn_ty
                          arity_alts = (zip
                              (subsequences fn_args)
                              (reverse $ map
                                  ((`mkFunTys` fn_ret) . reverse)
                                  (subsequences (reverse fn_args))
                                )
                            )
                      -- alternatives over function arity
                      in concatMap (\(fn_args', fn_ret') -> -- :: [Rand [[LHsExpr]]] -- alts-alts-args
                          case both (uncurry unify) ((fn_ret', arg0), (arg0, dropForAlls fn_ret')) of
                            (Just arg0_mapper, Just fn_mapper) ->
                                let next_exprs_alts = go n' (substTys (map2subst fn_mapper) argrest)
                                    subbed_fn_args = substTys (map2subst arg0_mapper) fn_args'
                                    subbed_fn_var = (`setVarType` (substTy (map2subst fn_mapper) fn_ty)) <$> fn_var
                                    this_exprs_alts = go (n' - 1) subbed_fn_args
                                in [ -- trace (ppr_unsafe (fn_args', subbed_fn_args)) $ 
                                    -- trace "OUTER OUTER " $
                                    do
                                      next_exprs <- next_exprs_alt
                                      this_exprs <- this_exprs_alt
                                      return [
                                          let fn_var_expr :: LHsExpr GhcTc
                                              fn_var_expr = (HsVar NoExt . noLoc) <$> subbed_fn_var
                                          in if null this_expr
                                              then (fn_var_expr : next_expr)
                                              else ((noLoc $ HsPar NoExt $ mk_app fn_var_expr this_expr) : next_expr)
                                          | this_expr <- this_exprs
                                          , next_expr <- next_exprs
                                        ]
                                    | next_exprs_alt <- next_exprs_alts
                                    , this_exprs_alt <- this_exprs_alts
                                  ] -- [Rand [LHsExpr GhcTc]]
                            _ -> mempty -- (Nothing, Nothing)
                            -- (l, r) -> error $ "Fwd and bkwd unification disagree: " ++ (ppr_unsafe fn_ret') ++ " is " ++ (ppr_unsafe l) ++ " vs. " ++ (ppr_unsafe arg0) ++ " is " ++ (ppr_unsafe r)
                        ) arity_alts
                    ) fn_tys
                  -- note that although we are iterating over function arities, the function alt under consideration in _this scope_ has fixed arity (see argrest) so we can zip all the alternatives we collect along the argument axis without loss of data
                ) target_funs
            ret = go n f0_args
        in fmap concat $ sequence $ map (fmap (map (\arglist ->
            if null arglist
              then f0_expr
              else mk_app f0_expr arglist
          ))) (ret)
      funs'' :: [[Located Id]]
      !funs'' = map (uncurry (map . (\(L l v) t -> L l (setVarType v t)))) $ funs
      
  in map (fmap concat . sequence . map (expand_fun depth)) funs''