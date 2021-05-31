
-- Copyright (c) 2020 Matthías Páll Gissurarson
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
module WRIT.Plugin ( plugin, module WRIT.Configure ) where

import WRIT.Configure

import Control.Monad (when, unless, guard, foldM, zipWithM, msum)
import Data.Maybe (mapMaybe, catMaybes, fromMaybe, fromJust, listToMaybe, isJust)
import Data.Either
import Data.IORef
import Data.List (nubBy, sortOn, intersperse, or, partition, minimumBy, maximumBy, sort)
import Control.Arrow ((&&&))
import Data.Function (on)
import Data.Kind (Constraint)
import Data.Data (Data, toConstr)
import Prelude hiding ((<>))
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Proxy
import Data.Dynamic
import Type.Reflection (someTypeRep)
import Text.Read (readMaybe)

import GHC.TypeLits(TypeError(..), ErrorMessage(..))

import Data.Coerce

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import System.IO.Unsafe (unsafePerformIO)

import Bag
import FV (fvVarListVarSet, fvVarSet)

#if __GLASGOW_HASKELL__ > 810
import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Plugin

import GHC.Tc.Types
import GHC.Tc.Types.Evidence
import GHC.Tc.Types.Constraint
import GHC.Tc.Utils.TcMType hiding (newWanted, newFlexiTyVar, zonkTcType)


import GHC.Core.TyCo.Rep
import GHC.Core.Predicate
import GHC.Core.Class

import GHC.Utils.Error

import GHC.Builtin.Types.Prim
import GHC.Builtin.Names

import GHC.Types.Id.Make

import GHC.Hs.Binds
import GHC.Hs.Extension
import GHC.Hs.Expr
import GHC.Types.EvTerm (evCallStack)

#else
import GhcPlugins hiding (TcPlugin)
import TcRnTypes
import TcPluginM
import ErrUtils (Severity(SevWarning))
import TcEvidence


import TysPrim
import PrelNames
import TyCoRep

import ClsInst
import Class
import Inst hiding (newWanted)

import MkId
import TcMType hiding (newWanted, newFlexiTyVar, zonkTcType)
import qualified TcMType as TcM

import TcType
import CoAxiom
import Unify
import TcHsSyn

import InstEnv

-- Holefits
import RdrName (globalRdrEnvElts)
import TcRnMonad (keepAlive, getLclEnv, getGlobalRdrEnv, getGblEnv, newSysName)
import TcHoleErrors
import PrelInfo (knownKeyNames)
import Data.Graph (graphFromEdges, topSort, scc)
import Control.Monad (filterM, replicateM)
import DsBinds (dsHsWrapper)
import DsMonad (initDsTc)

import TcEvTerm (evCallStack)

#if __GLASGOW_HASKELL__ >= 810
import GHC.Hs.Expr

#else

--- Dynamic
import HsBinds
import HsExtension
import HsExpr
-------

#endif

#if __GLASGOW_HASKELL__ < 810


-- Backported from 8.10
isEqPrimPred = isCoVarType
instance Outputable SDoc where
  ppr x = x

#else

import Constraint
import Predicate

#endif

#endif


--------------------------------------------------------------------------------
-- Exported

plugin :: Plugin
plugin = defaultPlugin { tcPlugin = Just . gritPlugin
                       , pluginRecompile = purePlugin
                       , installCoreToDos = coreDyn }

--------------------------------------------------------------------------------

data Log = Log { log_pred_ty :: Type, log_loc :: CtLoc}
         | LogDefault { log_pred_ty :: Type, log_loc :: CtLoc,
                        log_var :: Var, log_kind :: Kind, log_res :: Type }
         | LogMarshal { log_pred_ty :: Type, log_loc :: CtLoc, log_to_dyn :: Bool}
         | LogSDoc {log_pred_ty :: Type, log_loc :: CtLoc, log_msg :: SDoc}

logSrc :: Log -> RealSrcSpan
logSrc = ctLocSpan . log_loc

instance Ord Log where
  compare a@Log{} b@Log{} =
      if logSrc a == logSrc b
      then (compare `on` (showSDocUnsafe . ppr)) a b
      else (compare `on` logSrc) a b
  compare Log{} _ = LT
  compare _ Log{} = GT
  compare a@LogDefault{} b@LogDefault{} =
      if logSrc a == logSrc b
      then (compare `on` (showSDocUnsafe . ppr)) a b
      else (compare `on` logSrc) a b
  compare LogDefault{} _ = LT
  compare _ LogDefault{} = GT
  compare a@LogMarshal{} b@LogMarshal{} =
      if logSrc a == logSrc b
      then (compare `on` (showSDocUnsafe . ppr)) a b
      else (compare `on` logSrc) a b
  compare LogMarshal{} _ = LT
  compare _ LogMarshal{} = GT
  compare a@LogSDoc{} b@LogSDoc{} =
      if logSrc a == logSrc b
      then (compare `on` (showSDocUnsafe . ppr)) a b
      else (compare `on` logSrc) a b

instance Eq Log where
   a@Log{} == b@Log{} =
       ((==) `on` logSrc) a b && (eqType `on` log_pred_ty) a b
   Log{} == _ = False
   a@LogDefault{} == b@LogDefault{} =
       ((==) `on` logSrc) a b && (eqType `on` log_pred_ty) a b
                              && ((==) `on` log_var) a b
   LogDefault{} == _ = False
   a@LogMarshal{} == b@LogMarshal{} =
       ((==) `on` logSrc) a b && (eqType `on` log_pred_ty) a b
   LogMarshal{} == _ = False
   a@LogSDoc{} == b@LogSDoc{} =
       ((==) `on` logSrc) a b
       && (eqType `on` log_pred_ty) a b
       && ((==) `on` (showSDocUnsafe . log_msg)) a b
   LogSDoc{} == _ = False

instance Outputable Log where
   -- We do some extra work to pretty print the Defaulting messages
   ppr Log{..}
     | Just msg <- userTypeError_maybe log_pred_ty = pprUserTypeErrorTy msg
     | otherwise = text "WRIT" <+> ppr log_pred_ty
   ppr LogDefault{..} = fsep [ text "Defaulting"
                               -- We want to print a instead of a0
                             , quotes (ppr (mkTyVarTy log_var)
                                       <+> dcolon <+> ppr log_kind)
                             , text "to"
                             , quotes (ppr log_res)
                             , text "in"
                             , quotes (ppr log_pred_ty)]
      where printFlav Given = "Will default"
            printFlav _ = "Defaulting"
   ppr LogMarshal{..} = fsep [ text "Marshalling"
                             , quotes (ppr log_pred_ty)
                             , text (if log_to_dyn
                                     then "to Dynamic"
                                     else "from Dynamic") ]
   ppr LogSDoc{..} = log_msg

zonkLog :: Log -> TcPluginM Log
zonkLog log@Log{..} = do zonked <- zonkTcType log_pred_ty
                         return $ log{log_pred_ty=zonked}
-- We don't want to zonk LogDefault, since then we can't see what variable was
-- being defaulted.
zonkLog log = return log

logToErr :: Log -> TcPluginM Ct
logToErr Log{..} = mkWanted log_loc log_pred_ty
logToErr LogDefault{..} =
   do sDocToTyErr [ text "Defaulting"
                  , quotes (ppr (mkTyVarTy log_var)
                            <+> dcolon <+> ppr log_kind)
                  , text "to"
                  , quotes (ppr log_res)
                  , text "in"
                  , quotes (ppr log_pred_ty)] >>= mkWanted log_loc
logToErr LogMarshal{..} =
   do sDocToTyErr [ text "Marshalling"
                  , quotes (ppr (log_pred_ty))
                  , text (if log_to_dyn
                          then "to Dynamic"
                          else "from Dynamic") ] >>= mkWanted log_loc
logToErr LogSDoc{..} = sDocToTyErr [log_msg] >>= mkWanted log_loc

sDocToTyErr :: [SDoc] -> TcPluginM Type
sDocToTyErr docs =
  do txtCon <- promoteDataCon <$> tcLookupDataCon typeErrorTextDataConName
     appCon <- promoteDataCon <$> tcLookupDataCon typeErrorAppendDataConName
     dflags <- unsafeTcPluginTcM getDynFlags
     let txt str = mkTyConApp txtCon [mkStrLitTy $ fsLit str]
         sppr = txt . showSDoc dflags . ppr
         app ty1 ty2 = mkTyConApp appCon [ty1, ty2]
     mkTyErr $ foldl1 app $ map sppr $ intersperse (text " ") docs

addWarning :: DynFlags -> Log -> TcPluginM ()
addWarning dflags log = tcPluginIO $ warn (ppr log)
  where warn = putLogMsg dflags NoReason SevWarning
#if __GLASGOW_HASKELL__ > 810
                 (RealSrcSpan (logSrc log) Nothing)
#else
                 (RealSrcSpan (logSrc log)) (defaultErrStyle dflags)
#endif

data Flags = Flags { f_debug            :: Bool
                   , f_quiet            :: Bool
                   , f_keep_errors      :: Bool
                   , f_fill_holes :: Bool
                   , f_fill_hole_depth :: Int
                    } deriving (Show)

getFlags :: [CommandLineOption] -> Flags
getFlags opts = Flags { f_debug                 = "debug"            `elem` opts
                      , f_quiet                 = "quiet"            `elem` opts
                      , f_keep_errors           = "keep-errors"      `elem` opts
                      , f_fill_holes            = "fill-holes" `elem` opts
                      , f_fill_hole_depth       = getFillHoleDepth opts
                      }

getFillHoleDepth :: [CommandLineOption] -> Int
getFillHoleDepth [] = 0
getFillHoleDepth (o:opts)
 | ["fill-hole-depth", n] <- split '=' o =
   case readMaybe n of
       Just n -> n
       _ -> error "WRIT: Invalid fill-hole-depth parameter"
 | otherwise = getFillHoleDepth opts

pprOut :: Outputable a => String -> a -> TcPluginM ()
pprOut str a = do dflags <- unsafeTcPluginTcM getDynFlags
                  tcPluginIO $ putStrLn (str ++ " " ++ showSDoc dflags (ppr a))

gritPlugin :: [CommandLineOption] -> TcPlugin
gritPlugin opts = TcPlugin initialize solve stop
  where
    flags@Flags{..} = getFlags opts
    initialize = do
      when f_debug $ tcPluginIO $ putStrLn "Starting WRIT in debug mode..."
      when f_debug $ tcPluginIO $ print flags
      tcPluginIO $ newIORef Set.empty
    solve :: IORef (Set Log) -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
    solve warns given derived wanted = do
       dflags <- unsafeTcPluginTcM getDynFlags
       let pprDebug :: Outputable a => String -> a -> TcPluginM ()
           pprDebug str a = when f_debug $ pprOut str a
       pprDebug "Solving" empty
       pprDebug "-------" empty
       mapM_ (pprDebug "Given:") given
       mapM_ (pprDebug "Derived:") derived
       mapM_ (pprDebug "Wanted:") wanted
       pprDebug "-------" empty
       pluginTyCons <- getPluginTyCons
       let solveWFun :: ([Ct], ([(EvTerm, Ct)],[Ct], Set Log)) -> (SolveFun, String)
                     -> TcPluginM ([Ct], ([(EvTerm, Ct)],[Ct], Set Log))
           solveWFun (unsolved, (solved, more, logs)) (solveFun, explain) = do
             (still_unsolved, (new_solved, new_more, new_logs)) <-
               inspectSol <$> mapM (solveFun pluginTyCons) unsolved
             mapM_ (pprDebug (explain ++ "-sols")) new_solved
             mapM_ (pprDebug (explain ++ "-more")) new_more
             return (still_unsolved, (solved ++ new_solved,
                                      more ++ new_more,
                                      logs `Set.union` new_logs))
           order :: [(SolveFun, String)]
           order = [ (solveDynamic, "Discharging")
                   , (solveDefault,   "Defaulting")
                   , (solveDynamicTypeables,   "SDTs")
                   , (solveDynDispatch,   "Checking Dynamic Dispatch") ]
           to_check = wanted ++ derived
       (_, (solved_wanteds, more_cts, logs)) <-
          foldM solveWFun (to_check, ([],[],Set.empty)) order
       errs <- if f_keep_errors
               then mapM logToErr (Set.toAscList logs)
               else tcPluginIO $ modifyIORef warns (logs `Set.union`) >> mempty
       return $ TcPluginOk solved_wanteds (errs ++ more_cts)
    stop warns = do dflags <- unsafeTcPluginTcM getDynFlags
                    logs <- Set.toAscList <$> tcPluginIO (readIORef warns)
                    zonked_logs <- mapM zonkLog logs
                    unless f_quiet $ mapM_ (addWarning dflags) zonked_logs


data PluginTyCons = PTC { ptc_default :: TyCon
                        , ptc_dc :: DynCasts }

data DynCasts = DC { dc_typeable :: Class
                   , dc_dynamic :: TyCon
                   , dc_to_dyn :: Id
                   , dc_cast_dyn :: Id
                   , dc_has_call_stack :: TyCon
                   , dc_dyn_dispatch :: Id
                   , dc_sometyperep :: TyCon
                   , dc_sometyperep_dc :: DataCon
                   , dc_typerep :: Id }

getPluginTyCons :: TcPluginM PluginTyCons
getPluginTyCons =
   do fpmRes <- findImportedModule (mkModuleName "WRIT.Configure") Nothing
      dc_dynamic <- getTyCon dYNAMIC "Dynamic"
      dc_typeable <- getClass tYPEABLE_INTERNAL "Typeable"
      dc_sometyperep <- getTyCon tYPEABLE_INTERNAL "SomeTypeRep"
      dc_sometyperep_dc <- getDataCon tYPEABLE_INTERNAL "SomeTypeRep"
      dc_typerep <- getId tYPEABLE_INTERNAL "typeRep"
      dc_to_dyn <- getId dYNAMIC "toDyn"
      dc_has_call_stack <- getTyCon gHC_STACK_TYPES "HasCallStack"

      case fpmRes of
         Found _ mod  ->
             do ptc_default <- getTyCon mod "Default"
                dc_cast_dyn <- getId mod "castDyn"
                dc_dyn_dispatch <- getId mod "dynDispatch"
                let ptc_dc = DC {..}
                return PTC{..}
         NoPackage uid -> pprPanic "Plugin module not found (no package)!" (ppr uid)
         FoundMultiple ms -> pprPanic "Multiple plugin modules found!" (ppr ms)
         NotFound{..} -> pprPanic "Plugin module not found!" empty
  where getTyCon mod name = lookupOrig mod (mkTcOcc name) >>= tcLookupTyCon
        getDataCon mod name = lookupOrig mod (mkDataOcc name) >>= tcLookupDataCon
        getPromDataCon mod name = promoteDataCon <$> (getDataCon mod name)
        getClass mod name = lookupOrig mod (mkClsOcc name) >>= tcLookupClass
        getId mod name = lookupOrig mod (mkVarOcc name) >>= tcLookupId


type Solution = Either Ct (Maybe (EvTerm, Ct), -- The solution to the Ct
                           [Ct],               -- Possible additional work
                           Set Log)              -- What we did

type SolveFun = PluginTyCons -> Ct -> TcPluginM Solution

wontSolve :: Ct -> TcPluginM Solution
wontSolve = return . Left

couldSolve :: Maybe (EvTerm,Ct) -> [Ct] -> Set Log -> TcPluginM Solution
couldSolve ev work logs = return (Right (ev,work,logs))


-- Defaults any ambiguous type variables of kind k to l if Default k = l
solveDefault :: SolveFun
solveDefault ptc@PTC{..} ct =
  do defaults <- catMaybes <$> mapM getDefault (tyCoVarsOfCtList ct)
     if null defaults then wontSolve ct
      -- We make assertions that `a ~ def` for all free a in pred_ty of ct. and
      -- add these as new assertions. For meta type variables (i.e. ones that
      -- have been instantiated with a `forall`, e.g. `forall a. Less H a`), an
      -- assert is a derived, meaning that we emit a wanted that requires no
      -- evidence . E.g. when checking  `forall (a :: Label) . Less H a` and we
      -- have `type instance Default Label = L`, we emit a `a0 ~ L`.
      -- For skolems ("rigid" type variables like the a in `True :: F a Bool`),
      -- we cannot touch the variable so we cannot unify them with a derived. In
      -- that case, we emit a given, saying that `a ~ L` i.e. we essentially
      -- change the type of `True :: F a Bool` to `True :: a ~ L => F a Bool`.
      -- Note that we cannot simply emit a given for both, since we cannot
      -- mention a meta type variable in a given.
     else do let (eq_tys, logs) = unzip $ map mkTyEq defaults
             assert_eqs <- mapM mkAssert eq_tys
             couldSolve Nothing assert_eqs (Set.fromList logs)
   where mkAssert = either (mkDerived bump) (uncurry (mkGiven bump))
         bump = bumpCtLocDepth $ ctLoc ct
         getDefault var = fmap ((var,) . snd) <$> matchFam ptc_default [varType var]
         mkTyEq (var,def) = ( if isMetaTyVar var then Left pred_ty
                              else Right (pred_ty, proof),
                              LogDefault{log_pred_ty = ctPred ct,
                                         log_var = var, log_kind = varType var,
                                         log_res = def, log_loc =ctLoc ct})
           where EvExpr proof = mkProof "grit-default" (mkTyVarTy var) defApp
                 pred_ty = mkPrimEqPredRole Nominal (mkTyVarTy var) defApp
                 defApp = mkTyConApp ptc_default [varType var]

-- GHC doesn't know how to solve Typeable (Show Dynamic => Dynamic -> Int),
-- but in core it's the same as Show Dynamic -> Dynamic -> Int. So we simply
-- show that 'Show Dynamic' and 'Dynamic -> Int' are both typeable, and
-- construct the evidence that 'Show Dynamic => Dynamic -> Int' is thus
-- typeable.
solveDynamicTypeables :: SolveFun
solveDynamicTypeables ptc@PTC{..}
   ct | CDictCan{..} <- ct
      , cc_class == dc_typeable
      , [kind, ty] <- cc_tyargs
      , tcIsLiftedTypeKind kind
      , (res_ty, preds@(p:ps)) <- splitPreds ty
      , pts <- mapMaybe (splitTyConApp_maybe) preds
      , all (tcEqType dynamic) $ concatMap snd pts =
     do (r_typable_ev, r_typeable_ct) <- checkTypeable res_ty
        -- We don't want to check the constraints here, since we won't need
        -- them for the actual e.g. Show Dynamic, since we'll never
        -- call the function at Dynamic.
        -- constrs <- mapM (mkWanted (ctLoc ct)) preds
        t_preds <- mapM checkTypeablePred pts
        let (p_evs, p_cts) = unzip t_preds
            checks = r_typeable_ct:(concat p_cts)
            classCon = tyConSingleDataCon (classTyCon cc_class)
            r_ty_ev = EvExpr $ evId r_typable_ev
            (final_ty, proof) = foldr conTypeable (res_ty, r_ty_ev) p_evs
        couldSolve (Just (proof, ct)) checks Set.empty
     | otherwise = wontSolve ct
  where
     DC {..} = ptc_dc
     dynamic = mkTyConApp dc_dynamic []
     checkTypeablePred :: (TyCon, [Type]) -> TcPluginM ((Type, EvTerm), [Ct])
     checkTypeablePred (tc, tys) = do
       args_typeable <- mapM checkTypeable tys
       let (_, evcts) = unzip args_typeable
           ev = EvTypeableTyCon tc (map (EvExpr . evId . ctEvId) evcts)
           ty = mkTyConApp tc tys
       return ((ty, evTypeable ty ev), evcts)
     conTypeable :: (Type, EvTerm) -> (Type, EvTerm) -> (Type, EvTerm)
     conTypeable (fty, fterm) (argty, argterm) =
       let res_ty = mkTyConApp funTyCon [tcTypeKind fty, tcTypeKind argty, fty, argty]
           r_term = evTypeable res_ty $ EvTypeableTrFun fterm argterm
       in (res_ty, r_term)

     checkTypeable :: Type -> TcPluginM (EvId, Ct)
     checkTypeable ty = do
        c <- mkWanted (ctLoc ct) $ mkTyConApp (classTyCon dc_typeable) [tcTypeKind ty, ty]
        return (ctEvId c, c)


-- | Solves Γ |- C Dynamic
solveDynDispatch :: SolveFun
solveDynDispatch ptc@PTC{..} ct | CDictCan{..} <- ct
                                , [arg] <- cc_tyargs
                                , arg `tcEqType` dynamic = do
  class_insts <- flip classInstances cc_class <$> getInstEnvs
  let class_tys = map is_tys class_insts
  -- We can only dispatch on singe argument classes
  if not (all ((1 ==) . length) class_tys) then wontSolve ct
  else do
    -- Make sure we check any superclasses
    scChecks <- mapM (mkWanted (ctLoc ct) .
                      flip piResultTys cc_tyargs .
                      mkSpecForAllTys (classTyVars cc_class))
                      $ classSCTheta cc_class
    let scEvIds = map (evId . ctEvId) scChecks
    args_n_checks <- mapM (methodToDynDispatch cc_class class_tys)
                          (classMethods cc_class)
    let log = Set.empty
        classCon = tyConSingleDataCon (classTyCon cc_class)
        (args, checks) = unzip args_n_checks
        proof = evDataConApp classCon cc_tyargs $ scEvIds ++ args
    couldSolve (Just (proof, ct)) (scChecks ++ concat checks) log
                               | otherwise = wontSolve ct
  where
     DC {..} = ptc_dc
     dynamic = mkTyConApp dc_dynamic []
     sometyperep = mkTyConApp dc_sometyperep []
     -- | The workhorse. Creates the dictonary for C Dynamic on the fly.
     methodToDynDispatch :: Class
                         -> [[Type]]
                         -> Id
                         -> TcPluginM (EvExpr, [Ct])
     -- For method 'loo :: Show a => Int -> a -> Int -> Int' in Foo with instances
     -- Foo A and Foo B, this will generate the following (in Core):
     -- Notation: {Foo A} = The dictionary for Foo A
     -- (\ (k :: Show Dynamic) (l :: Int) (m :: Dynamic) ->
     --   dynDispatch @(Show Dynamic => Int -> Dynamic -> Int -> Int)
     --               {Typeable (Show Dynamic => Int -> Dynamic -> Int -> Int)}
     --               -- ^ Only used too lookup in the table
     --               [ (SomeTypeRep (typeRep :: TypeRep A), -- In core
     --                  toDyn @(Show Dynamic => Int -> Dynamic -> Int -> Int)
     --                        {Typeable (Show Dynamic => Int -> Dynamic -> Int -> Int)}
     --                        (\ (k :: Show Dynamic) (l :: Int) (m :: Dynamic) ->
     --                           loo @A {Foo A} {Show A} l (castDyn m)))
     --               , (SomeTypeRep (typeRep :: TypeRep B), -- In core
     --                  toDyn @(Show Dynamic => Int -> Dynamic -> Int -> Int)
     --                        {Typeable (Show Dynamic => Int -> Dynamic -> Int -> Int)}
     --                        (\ (k :: Show Dynamic) (l :: Int) (m :: Dynamic) ->
     --                           loo @B {Foo B} {Show B} l (castDyn m)))]
     --               -- ^ The dynamic dispatch table
     --               "loo"
     --               -- ^ The name of the function. Used for better error messages.
     --               "Foo"
     --               -- ^ The name of the class. Used for better error messages.
     --               (m :: Dynamic)
     --               -- ^ The dynamic value to dispatch on
     --               (runtimeError @(Show Dynamic) "Should never be evaluated!")
     --               -- ^ Provided to please the type gods. This dictionary
     --               --   is just thrown away by the function after dispatch.
     --               (l :: Int)
     --               -- ^ The first argument to the function, captured before
     --               --   we had the dynamic we could use to know which type
     --               --   to dispatch on.
     --               (m :: Dynamic)
     --               -- ^ The dynamic again. This will go to a castDyn to the
     --               --   proper type before being evaluated at the function.
     -- )
     -- And similar entries for each function in the Foo class.
     --
     -- When given a dynamic (Dynamic (tr :: TypeRep a) (v :: a)), dynDispatch
     -- looks up  (SomeTypeRep tr :: SomeTypeRep) in the dispatch table.
     -- If it finds a function 'f' that matches, it converts it to the expected
     -- value with 'fromDyn f', if possible, and emits a runtime error otherwise.
     -- If a function with the matching type is not found, it also emits a
     -- runtime error, saying that no matching instance was found.
     methodToDynDispatch cc_class class_tys fid = do
       -- Names included for better error messages.
       let fname = (occNameFS (getOccName fid))
           cname = (occNameFS (getOccName cc_class))
       fun_name <- unsafeTcPluginTcM $ mkStringExprFS fname
       class_name <- unsafeTcPluginTcM $ mkStringExprFS cname
       let (tvs, ty) = tcSplitForAllVarBndrs (varType fid)
           (res, preds) = splitPreds ty
           bound_preds = map (mkForAllTys tvs) preds
           dpt_ty = mkBoxedTupleTy [sometyperep, dynamic]
           fill_ty = piResultTys (mkForAllTys tvs res)
           enough_dynamics = replicate (length $ head class_tys) dynamic
           dyn_ty = fill_ty enough_dynamics
           -- Whole ty is the type minus the Foo a in the beginning
           whole_ty = funResultTy $ piResultTys (varType fid) enough_dynamics
           unsatisfied_preds =map (flip piResultTy dynamic) $  drop 1 bound_preds
           mkMissingDict t = mkRuntimeErrorApp rUNTIME_ERROR_ID t "Dynamic dictonary shouldn't be evaluated!"
           dynb_pred_dicts = map mkMissingDict unsatisfied_preds
       dyn_pred_vars <- unsafeTcPluginTcM $ mapM (mkSysLocalM (getOccFS fid)) unsatisfied_preds
       let mkDpEl :: Type -> [CoreBndr]  -> [Type] -> TcPluginM (CoreExpr, [Ct])
           mkDpEl res_ty revl dts@[dp_ty] =
              do (tev, check_typeable) <- checkTypeable whole_ty
                 (dptev, check_typeable_dp) <- checkTypeable dp_ty
                 check_preds <- mapM (mkWanted (ctLoc ct) . flip piResultTys dts) bound_preds
                 let dyn_app = mkCoreApps (Var dc_to_dyn) [Type whole_ty, Var tev]
                     pevs = map ctEvId check_preds
                     fapp = mkCoreApps (Var fid) $ [Type dp_ty] ++ (map Var pevs)
                     toFappArg :: (Type, Type, CoreBndr) -> TcPluginM (CoreExpr, [Ct])
                     toFappArg (t1,t2,b) | tcEqType t1 t2 = return (Var b, [])
                                         |  otherwise  = do
                         (tev, check_typeable) <- checkTypeable t2
                         ccs <- mkWanted (ctLoc ct) $ mkTyConApp dc_has_call_stack []
                         cs <- mkFromDynErrCallStack dc_cast_dyn ct $ ctEvEvId $ ctEvidence ccs
                         let app = mkCoreApps (Var dc_cast_dyn)
                                       [Type t2, Var tev, cs, Var b]
                         return (app,[check_typeable, ccs])
                     matches :: [CoreBndr] -> Type -> [(Type, Type, CoreBndr)]
                     matches [] _ = []
                     matches (b:bs) ty = (varType b, t, b):(matches bs r)
                       where (t,r) = splitFunTy ty -- Safe, binders are as long or longer.
                 (fappArgs, fappChecks) <- unzip <$> mapM toFappArg (matches revl res_ty)
                 let dfapp = mkCoreApps dyn_app [mkCoreLams (dyn_pred_vars ++ revl) $ mkCoreApps fapp fappArgs]
                     trapp = mkCoreApps (Var dc_typerep) [Type (tcTypeKind dp_ty), Type dp_ty, Var dptev]
                     strapp = mkCoreApps
                                 (Var (dataConWrapId dc_sometyperep_dc))
                                 [Type (tcTypeKind dp_ty), Type dp_ty, trapp]
                     checks = [check_typeable, check_typeable_dp] ++ check_preds ++ (concat fappChecks)
                     tup = mkCoreTup [strapp, dfapp]
                 return (tup, checks)
           -- | The workhorse that constructs the dispatch tables.
           mkDpEl _ _ tys = pprPanic "Multi-param typeclasses not supported!" $ ppr tys
           finalize (dp:lams) res_ty = do
             let revl = reverse (dp:lams)
                 mkFunApp a b = mkTyConApp funTyCon [tcTypeKind a,tcTypeKind b, a, b]
             (tev, check_typeable) <- checkTypeable whole_ty
             dpt_els_n_checks <- mapM (\ct -> mkDpEl (fill_ty ct) revl ct) class_tys
             -- To make the types match up, we must make a dictionary for each of the predicates,
             -- even though these will never be used.
             let (dpt_els, dpt_checks) = unzip dpt_els_n_checks
                 app = mkCoreApps (Var dc_dyn_dispatch)
                         ([ Type whole_ty, evId tev, mkListExpr dpt_ty dpt_els
                         , fun_name, class_name, Var dp]
                         ++ dynb_pred_dicts
                         ++ (map Var revl))
                 checks = (check_typeable:(concat dpt_checks))
                 -- TODO app to pred dicts
                 lamApp = mkCoreLams (dyn_pred_vars ++ revl) app
             return $ (lamApp, checks)
           -- We figure out all the arguments to the functions first from the type.
           loop lams ty = do
             case splitFunTy_maybe ty of
                Just (t,r) -> do
                  bid <- unsafeTcPluginTcM $ mkSysLocalM (getOccFS fid) t
                  loop (bid:lams) r
                _ -> finalize lams ty
       res <- loop [] dyn_ty
       -- If there's a method we can't covert (e.g. due to it's type not
       -- being Typeable), the entire core we generate will be incorrect,
       -- so we have to abort. Otherwise, we get a cryptic Typeable error.
       -- Best would be if we customized said error to say something like
       -- "Dynamic dispatch for Foo failed due to loo :: Show a => a -> Int"
       return res

     checkTypeable :: Type -> TcPluginM (EvId, Ct)
     checkTypeable ty = do
        c <- mkWanted (ctLoc ct) $ mkTyConApp (classTyCon dc_typeable) [tcTypeKind ty, ty]
        return (ctEvId c, c)

splitPreds :: Type -> (Type, [PredType])
splitPreds ty =
  case tcSplitPredFunTy_maybe ty of
    Just (pt, t) -> (pt:) <$> splitPreds t
    _ -> (ty, [])

mkTyErr ::  Type -> TcPluginM Type
mkTyErr msg = flip mkTyConApp [typeKind msg, msg] <$>
                 tcLookupTyCon errorMessageTypeErrorFamName

-- | Creates a type error with the given string at the given loc.
mkTypeErrorCt :: CtLoc -> String -> TcPluginM Ct
mkTypeErrorCt loc str =
  do txtCon <- promoteDataCon <$> tcLookupDataCon typeErrorTextDataConName
     appCon <- promoteDataCon <$> tcLookupDataCon typeErrorAppendDataConName
     vappCon <- promoteDataCon <$> tcLookupDataCon  typeErrorVAppendDataConName
     let txt str = mkTyConApp txtCon [mkStrLitTy $ fsLit str]
         app ty1 ty2 = mkTyConApp appCon [ty1, ty2]
         vapp ty1 ty2 = mkTyConApp vappCon [ty1, ty2]
         unwty = foldr1 app . map txt . intersperse " "
         ty_err_ty = foldr1 vapp $ map unwty $ map words $ lines str
     te <- mkTyErr ty_err_ty
     mkWanted loc te

getErrMsgCon :: TcPluginM TyCon
getErrMsgCon = lookupOrig gHC_TYPELITS (mkTcOcc "ErrorMessage") >>= tcLookupTyCon
-- Utils
mkDerived :: CtLoc -> PredType -> TcPluginM Ct
mkDerived loc eq_ty = flip setCtLoc loc . CNonCanonical <$> newDerived loc eq_ty

mkWanted :: CtLoc -> PredType -> TcPluginM Ct
mkWanted loc eq_ty = flip setCtLoc loc . CNonCanonical <$> newWanted loc eq_ty

mkGiven :: CtLoc -> PredType -> EvExpr -> TcPluginM Ct
mkGiven loc eq_ty ev = flip setCtLoc loc . CNonCanonical <$> newGiven loc eq_ty ev

mkProof :: String -> Type -> Type -> EvTerm
mkProof str ty1 ty2 = evCoercion $ mkUnivCo (PluginProv str) Nominal ty1 ty2

splitEquality :: Type -> Maybe (Kind, Type, Type)
splitEquality pred =
  do (tyCon, [k1, k2, ty1,ty2]) <- splitTyConApp_maybe pred
     guard (tyCon == eqPrimTyCon)
     guard (k1 `eqType` k2)
     return (k1, ty1,ty2)

inspectSol :: Ord d => [Either a (Maybe b, [c], Set d)]
           -> ([a], ([b], [c], Set d))
inspectSol xs = (ls, (catMaybes sols, concat more, Set.unions logs))
  where (ls, rs) = partitionEithers xs
        (sols, more, logs) = unzip3 rs

hasInst :: Type -> TcPluginM Bool
hasInst ty = case splitTyConApp_maybe ty of
              Just (tc, args) -> isJust <$> matchFam tc args
              _ -> return False

----------------------------------------------------------------
-- Marshalling to and from Dynamic
----------------------------------------------------------------
-- | Solves Γ |- (a :: Type) ~ (b :: Type) if a ~ Dynamic or b ~ Dynamic
solveDynamic :: SolveFun
solveDynamic ptc@PTC{..} ct
 | Just (k1,ty1,ty2) <- splitEquality (ctPred ct) = do
    let DC {..} = ptc_dc
        dynamic = mkTyConApp dc_dynamic []
        kIsType = tcIsLiftedTypeKind k1
        isDyn ty = ty `tcEqType` dynamic
    if kIsType && (isDyn ty1 || isDyn ty2)
    then marshalDynamic k1 ty1 ty2 ptc ct
    else wontSolve ct
  | otherwise = wontSolve ct

data PluginState = PS { evMap :: Map FastString EvExpr , next :: Int }

-- Global IORef Hack used to pass information between phases, as recommended at HIW.
pluginState :: IORef (PluginState)
{-# NOINLINE  pluginState#-}
pluginState = unsafePerformIO (newIORef (PS Map.empty 0))

addDynExpr :: String -> EvExpr -> IO String
addDynExpr base ev = do ps@((PS {..})) <- readIORef pluginState
                        let marker = mkFastString (base ++ "-" ++ show next)
                        writeIORef pluginState $
                           ( PS { next = next + 1
                                , evMap = Map.insert marker ev evMap })
                        return $ unpackFS marker

getDynExpr :: String -> IO (Maybe  EvExpr)
getDynExpr marker =  do PS{..} <- readIORef pluginState
                        return $ Map.lookup (mkFastString marker) evMap

marshalDynamic :: Kind -> Type -> Type -> SolveFun
marshalDynamic k1 ty1 ty2 PTC{..} ct =
   do let DC {..} = ptc_dc
          dynamic = mkTyConApp dc_dynamic []
          isDyn ty = ty `tcEqType` dynamic
          relTy = if isDyn ty1 then ty2 else ty1
          log = Set.singleton (LogMarshal relTy (ctLoc ct) (isDyn ty2))
          hasTypeable = mkTyConApp (classTyCon dc_typeable) [k1, relTy]
          hasCallStack = mkTyConApp dc_has_call_stack []
      -- we emit a proof with a very specific tag,
      -- which we then use later.
      -- However, since we don't refer to this until later
      -- we need to make sure that the EvVar is marked as exported.
      check_typeable <- exportWanted <$> mkWanted (ctLoc ct) hasTypeable
      check_call_stack <- exportWanted <$> mkWanted (ctLoc ct) hasCallStack
      -- We want the runtime errors to point to where the coerceDyn
      -- is happening .
      callStack <- mkFromDynErrCallStack dc_cast_dyn ct $
              ctEvEvId $ ctEvidence check_call_stack
      let typeableDict = ctEvEvId $ ctEvidence check_typeable
          evExpr = if isDyn ty1
                   then mkApps (Var dc_cast_dyn) [Type relTy, Var typeableDict
                                                 , callStack]
                   else mkApps (Var dc_to_dyn) [Type relTy, Var typeableDict]
      marker <- tcPluginIO $ addDynExpr "grit-dynamic" evExpr
      let proof = if isDyn ty1 then mkProof marker dynamic relTy
                               else mkProof marker relTy dynamic
      couldSolve (Just (proof, ct)) [ check_typeable , check_call_stack] log

exportWanted :: Ct -> Ct
exportWanted (CNonCanonical (w@CtWanted {ctev_dest = EvVarDest var}))
 = CNonCanonical (w{ctev_dest = EvVarDest (setIdExported var)})

mkFromDynErrCallStack :: Id -> Ct -> EvVar -> TcPluginM EvExpr
mkFromDynErrCallStack fdid ct csDict =
  flip mkCast coercion <$>
     (unsafeTcPluginTcM $ evCallStack (EvCsPushCall name loc var))
  where name = idName fdid
        loc = ctLocSpan (ctLoc ct)
        var = Var csDict
        coercion = mkSymCo (unwrapIP (exprType var))

-- Post-processing for Dynamics
coreDyn :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
coreDyn clo tds = do
  return $ (CoreDoPluginPass "WRIT" $ bindsOnlyPass addDyn):tds
  where Flags {..} = getFlags clo
        addDyn :: CoreProgram -> CoreM CoreProgram
        addDyn program = mapM addDynToBind program

        addDynToBind :: CoreBind -> CoreM CoreBind
        addDynToBind (NonRec b expr) = NonRec b <$> addDynToExpr expr
        addDynToBind (Rec as) = do
          let (vs, exprs) = unzip as
          nexprs  <- mapM addDynToExpr exprs
          return (Rec $ zip vs nexprs)

        addDynToExpr :: Expr Var -> CoreM (Expr Var)
        addDynToExpr (App expr arg) = do
           nexpr <- addDynToExpr expr
           narg <- addDynToExpr arg
           return (App nexpr narg)
        addDynToExpr (Lam b expr) = do
           Lam b <$> addDynToExpr expr
        addDynToExpr (Let binds expr) = do
          do nbs <- addDynToBind binds
             nexpr <- addDynToExpr expr
             return (Let nbs nexpr)
        addDynToExpr (Case expr b ty alts) =
          do nexpr <- addDynToExpr expr
             nalts <- mapM addDynToAlt alts
             return (Case nexpr b ty nalts)
        addDynToExpr (Tick t expr) = Tick t <$> addDynToExpr expr
        addDynToExpr orig@(Cast expr coercion) = do
          nexpr <- addDynToExpr expr
          case coercion of
            UnivCo (PluginProv prov) r t1 t2 ->
              (liftIO $ getDynExpr prov) >>= \case
                Just expr ->
                  do let res = App expr nexpr
                     when f_debug $
                       liftIO $ putStrLn $ showSDocUnsafe $
                       text "Replacing" <+> parens (ppr orig)
                       <+> text "with" <+> parens (ppr res)
                     return res
                Nothing -> return (Cast nexpr coercion)
            _ -> return (Cast nexpr coercion)
        addDynToExpr no_sub_expr = return no_sub_expr
        addDynToAlt :: (AltCon, [Var], Expr Var) ->
                       CoreM (AltCon, [Var], Expr Var)
        addDynToAlt (c, bs, expr) =
            do nexpr <- addDynToExpr expr
               return (c, bs, nexpr)
