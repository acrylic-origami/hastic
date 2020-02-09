{-# LANGUAGE LambdaCase, Rank2Types, NamedFieldPuns, TupleSections , MultiWayIf, BangPatternss #-}
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
import System.Random ( randomRIO )
import System.Random.Shuffle ( shuffle )

import Data.Bitraversable
import Data.Foldable ( foldrM )
import Control.Arrow ( (&&&), (***), first, second )
import Control.Monad ( join )
import Control.Monad.Trans ( MonadTrans(..) )
import Control.Monad.Trans.Maybe ( MaybeT(..) )
import Data.Semigroup ( mtimesDefault )
import Data.Maybe
import Data.Generics hiding ( TyCon, empty )
import Data.Generics.Extra ( GenericQT(..), gmapQT, mkQT )
import Data.List ( uncons, subsequences )
import Control.Applicative ( Applicative(..), Alternative(..), (<|>) )
import Data.Functor ( ($>) )

import Data.IntMap ( IntMap(..) )
import qualified Data.IntMap as IM
import Data.Map.Strict ( Map(..) )
import qualified Data.Map.Strict as M

import Hastic.Util
import Hastic.Lang

import Debug.Trace ( trace )

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

unify :: Type -> Type -> Maybe (Map Id Type, Map Id Type)
unify x y = liftA2 (,) (unify' y x) (unify' x y) where -- sorry for flipped args, felt like it made sense to make the first arg the concrete one first
  unify' a b = -- only bind `b` to more specific aspects of `a`
    let ((app_con_a, app_args_a), (app_con_b, app_args_b)) = both splitAppTys (a, b) -- NOTE also splits funtys annoyingly
        masum :: [(Type, Type)] -> Maybe (Map Id Type)
        masum = foldrM (flip (fmap . M.union) . uncurry unify') mempty
    in if | null app_args_b
          , Just bvar <- getTyVar_maybe b -> Just (M.singleton bvar a) -- `b` is totally free (or something else unexpected)
          | Just (tycon_a, tyargs_a) <- splitTyConApp_maybe a -- `a` is a true TyCon
          -> case splitTyConApp_maybe b of
            Just (tycon_b, tyargs_b) -- `b` is also a true TyCon
              | tycon_a == tycon_b
              -> masum $ zip tyargs_a tyargs_b
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
        FunBind { fun_id, fun_matches } -> [(s, fun_id)]
        _ -> mempty
      ) :: HsBind GhcTc -> [Fun])

concretize :: Int -> ClassInstMap -> Fun -> Maybe (Located Id, [Type])
concretize depth inst_map raw_fun = fmap (snd raw_fun,) $ uncurry ((tyfind depth .) . TFState) $ second (varType . unLoc) raw_fun where
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
                    m_inst_subst_map = fmap snd $ foldr (liftA2 (<>) . uncurry unify) (Just mempty) (zip cn_argsr inst_argsr)
                in case m_inst_subst_map of
                  Just inst_subst_map ->
                    let inst_subst = map2subst inst_subst_map
                        subbed_ctx_rest' = map (second (substTy inst_subst *** substTys inst_subst)) ctx_rest
                        subbed_inst_ctx = map (second (substTy inst_subst *** substTys inst_subst)) cns'
                    in tyfind (n - 1) $ TFState {
                      ctx = subbed_ctx_rest' <> subbed_inst_ctx,
                      sig = fromMaybe sig $ flip substTy sig <$> m_sig_subst
                    }
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

analyze :: Int -> ClassInstMap -> [(Located Id, [Type])] -> IO [LHsExpr GhcTc]
analyze depth inst_map funs =
  let expand_fun :: Int -> Located Id -> IO AppTree
      expand_fun 0 _ = return (BT bot_var mempty)
      expand_fun n f0 =
        let (f0_args, _f0_ret) = splitFunTys (varType $ unLoc f0)
            go :: Int -> [Type] -> IO [[AppTree]]
            go 0 args = return $ map (const [BT bot_var mempty]) args
            go n' [] = return mempty
            go n' (arg0:argrest) =
              foldr (\(fn_var, fn_tys) acc -> do -- IO [[[BiTree Id]]]: alts-args-alts
                  argshuffle <- reverse <$> mapM (randomRIO . (0,)) [1..(length fn_tys - 1)]
                  -- have to use IO: MaybeT handling of Nothing (via conjunction) isn't what we want
                  -- alternatives over function synthesized type definitions
                  arg_alts <- concat <$> mapM (\fn_ty -> do
                      let (fn_args, fn_ret) = splitFunTys fn_ty
                          arity_alts = (zip
                              (subsequences fn_args)
                              (reverse $ map
                                  ((`mkFunTys` fn_ret) . reverse)
                                  (subsequences (reverse fn_args))
                                )
                            )
                      -- alternatives over function arity
                      catMaybes <$> ( -- [[[AppTree]]]
                          sequence $ map (\(fn_args', fn_ret') -> runMaybeT $ do -- :: Maybe [[AppTree]] -- inner: alts; outer: args
                              (arg0_mapper, fn_mapper) <- liftM $ both map2subst <$> unify arg0 fn_ret'
                              this_exprs <- lift $ go (n' - 1) (substTys fn_mapper fn_args')
                              next_exprs <- lift $ go n' (substTys arg0_mapper argrest)
                              return ([BT fn_var this_exprs] : next_exprs)
                            ) arity_alts
                        )
                    ) (take (max 1 $ length fn_tys `div` 8) $ shuffle fn_tys argshuffle)
                  -- note that although we are iterating over function arities, the function alt under consideration in _this scope_ has fixed arity (see argrest) so we can zip all the alternatives we collect along the argument axis without loss of data
                  return $ foldl ((map (uncurry (++)) .) . zip) acc arg_alts
                ) (cycle [[]]) funs
        in BT f0 <$> go n f0_args
      flat_funs :: [Located Id]
      !flat_funs = concatMap' (uncurry (map . (\(L l v) t -> L l (setVarType v t)))) $ funs
      
  in concat <$> (mapM (fmap apptree_ast . expand_fun depth) flat_funs)