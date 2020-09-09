-- Copyright (c) 2020 Matthías Páll Gissurarson
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
module WRIT.Plugin ( plugin, module WRIT.Configure ) where

import WRIT.Configure

import Control.Monad (when, unless, guard, foldM, zipWithM, msum)
import Data.Maybe (mapMaybe, catMaybes, fromMaybe, fromJust, listToMaybe, isJust)
import Data.Either
import Data.IORef
import Data.List (intersperse, or)
import Data.Function (on)
import Data.Kind (Constraint)
import Data.Data (Data, toConstr)
import Prelude hiding ((<>))
import qualified Data.Set as Set
import Data.Set (Set)

import GHC.TypeLits(TypeError(..), ErrorMessage(..))

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

--- PostProcess
import GHC.Hs.Binds
import GHC.Hs.Extension
import GHC.Hs.Expr
-------

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

import TcType
import CoAxiom
import Unify


--- PostProcess
import HsBinds
import HsExtension
import HsExpr
import Bag
-------

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
                       , typeCheckResultAction = postProcess }

--------------------------------------------------------------------------------

data Log = Log { log_pred_ty :: Type, log_loc :: CtLoc}
         | LogDefault { log_pred_ty :: Type, log_loc :: CtLoc,
                        log_var :: Var, log_kind :: Kind, log_res :: Type }

logSrc :: Log -> RealSrcSpan
logSrc = ctLocSpan . log_loc

instance Ord Log where
  compare a b = if logSrc a == logSrc b
                then case (a,b) of
                  (Log{}, LogDefault{}) -> GT
                  (LogDefault{}, Log{}) -> LT
                  (_, _) -> EQ
                else compare (logSrc a) (logSrc b)

instance Eq Log where
   Log{} == LogDefault{} = False
   LogDefault{} == Log{} = False
   a@Log{} == b@Log{} =
       ((==) `on` logSrc) a b && (eqType `on` log_pred_ty) a b
   a@LogDefault{} == b@LogDefault{} =
       ((==) `on` logSrc) a b && (eqType `on` log_pred_ty) a b
                              && ((==) `on` log_var) a b

instance Outputable Log where
   -- We do some extra work to pretty print the Defaulting messages
   ppr Log{..} =
        case userTypeError_maybe log_pred_ty of
           Just msg -> pprUserTypeErrorTy msg
           _ -> text "WRIT" <+> ppr log_pred_ty
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

data Flags = Flags { f_debug        :: Bool
                   , f_quiet        :: Bool
                   , f_keep_errors  :: Bool } deriving (Show)

getFlags :: [CommandLineOption] -> Flags
getFlags opts = Flags { f_debug        = "debug"          `elem` opts
                      , f_quiet        = "quiet"          `elem` opts
                      , f_keep_errors  = "keep-errors"    `elem` opts }

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
           pprDebug str a = when f_debug $
               tcPluginIO $ putStrLn (str ++ " " ++ showSDoc dflags (ppr a))
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
           order = [ (solveOnlyIf,    "OnlyIf")
                   , (solveDischarge, "Discharging")
                   , (solveIgnore,    "Ignoring")
                   , (solveDefault,   "Defaulting") ]
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
                        , ptc_promote :: TyCon
                        , ptc_only_if :: TyCon
                        , ptc_ignore  :: TyCon
                        , ptc_discharge  :: TyCon
                        , ptc_msg :: TyCon
                        , ptc_dc :: DynCasts }

data DynCasts = DC { dc_typeable :: Class
                   , dc_dynamic :: TyCon
                   , dc_to_dyn :: Id
                   , dc_from_dyn :: Id}

getPluginTyCons :: TcPluginM PluginTyCons
getPluginTyCons =
   do fpmRes <- findImportedModule (mkModuleName "WRIT.Configure") Nothing

      dc_dynamic <- getTyCon dYNAMIC "Dynamic"
      dc_to_dyn <- getId dYNAMIC "toDyn"
      dc_from_dyn <- getId dYNAMIC "fromDyn"
      dc_typeable <- getClass tYPEABLE_INTERNAL "Typeable"
      let ptc_dc = DC {..}

      case fpmRes of
         Found _ mod  ->
             do ptc_default <- getTyCon mod "Default"
                ptc_discharge  <- getTyCon mod "Discharge"
                ptc_promote <- getTyCon mod "Promote"
                ptc_ignore  <- getTyCon mod "Ignore"
                ptc_msg     <- getPromDataCon mod "Msg"
                ptc_only_if <- getPromDataCon mod "OnlyIf"
                return PTC{..}
         NoPackage uid -> pprPanic "Plugin module not found (no package)!" (ppr uid)
         FoundMultiple ms -> pprPanic "Multiple plugin modules found!" (ppr ms)
         NotFound{..} -> pprPanic "Plugin module not found!" empty
  where getTyCon mod name = lookupOrig mod (mkTcOcc name) >>= tcLookupTyCon
        getPromDataCon mod name = promoteDataCon <$>
           (lookupOrig mod (mkDataOcc name) >>= tcLookupDataCon)
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

-- Solves Γ |- c :: Constraint if Γ |- Ignore c ~ Msg m, *where c is an empty class*
solveIgnore :: SolveFun
solveIgnore _ ct@CDictCan{..} | not (null $ classMethods cc_class) = wontSolve ct
solveIgnore ptc@PTC{..} ct@CDictCan{..} = do
  let ignore = mkTyConApp ptc_ignore [ctPred ct]
  hasIgnore <- hasInst ignore
  if not hasIgnore then wontSolve ct
  else do (msg_check, msg_var) <- checkMsg ptc ct ignore
          let log = Set.singleton (Log msg_var (ctLoc ct))
              classCon = tyConSingleDataCon (classTyCon cc_class)
              proof = evDataConApp classCon cc_tyargs []
          couldSolve (Just (proof, ct)) [msg_check] log
solveIgnore _ ct = wontSolve ct


-- Solves Γ |- (a :: k) ~ (b :: k) if Γ |- Discharge a b ~ Msg m.
solveDischarge :: SolveFun
solveDischarge ptc@PTC{..} ct =
  case splitEquality (ctPred ct) of
    Just (k1,ty1,ty2) -> do
      let discharge = mkTyConApp ptc_discharge [k1, ty1, ty2]
      hasDischarge <- hasInst discharge
      -- If k is Type, then we are doing a promotion, since the only valid
      -- instance Discharge (a :: *) (b :: *) comes from WRIT.Configure,
      -- where we have:
      --
      -- ```
      --    type instance Discharge (a :: *) (b :: *) =
      --       OnlyIf (Coercible a b) (Promote a b)
      -- ```
      --
      -- But since we don't want to introduce non-determinisim in our rules (or
      -- a separate rule for promote with some wonky condition on the kind), we
      -- don't do this check here at the cost of slightly worse error messages.
      let promote = mkTyConApp ptc_promote [ty1, ty2]
          kIsType = tcIsLiftedTypeKind k1
          DC {..} = ptc_dc
          isDyn ty = ty `tcEqType` mkTyConApp dc_dynamic []
      missingPromote <- (&&) kIsType . not <$> hasInst promote
      if not hasDischarge || missingPromote
      then if isDyn ty1 || isDyn ty2
           then do let relTy = if isDyn ty1 then ty2 else ty1
                       log = Set.singleton (Log relTy (ctLoc ct))
                       hasTypeable  = mkTyConApp (classTyCon dc_typeable) [k1, relTy]
                       proof = if isDyn ty1
                               then mkFromDynCast ptc_dc relTy
                               else mkToDynCast ptc_dc relTy
                       ev = ctEvidence ct
                       env = ctLocEnv $ ctLoc ct
                       evid = ctEvId ct

                   check_typeable <- mkWanted (ctLoc ct) hasTypeable
                   couldSolve (Just (proof, ct)) [check_typeable] log
           else wontSolve ct
      else do (msg_check, msg_var) <- checkMsg ptc ct discharge
              let log = Set.singleton (Log msg_var (ctLoc ct))
                  proof = mkProof "grit-discharge" ty1 ty2
              couldSolve (Just (proof, ct)) [msg_check] log
    _ -> wontSolve ct

mkToDynCast :: DynCasts -> Type -> EvTerm
mkToDynCast DC{..} ty = evCoercion coercion --mkEvCast exp coercion
  where coercion = mkUnivCo (PluginProv "grit-dynamic")
                            Nominal ty dynamic
        dynamic = mkTyConApp dc_dynamic []
        exp = evId dc_to_dyn

mkFromDynCast :: DynCasts -> Type -> EvTerm
mkFromDynCast DC{..} ty = evCoercion coercion
  where coercion = mkUnivCo (PluginProv "grit-dynamic")
                            Nominal dynamic ty
        dynamic = mkTyConApp dc_dynamic []
        exp = evId dc_from_dyn

-- Solve only if solves Γ |- OnlyIf c m_a ~ m_b, by checking  Γ |- c and
-- Γ |-  m_a ~ m_b
solveOnlyIf :: SolveFun
solveOnlyIf PTC{..} ct =
  case splitEquality (ctPred ct) of
    Just (k1,ty1,ty2) -> do
        -- As an optimization to avoid the constraint solver having to do too
        -- many loops, we unwrap any nested OnlyIfs here, and gather all the
        -- constraints.
        case reverse (unwrapOnlyIfs ty1) of
          [_] -> wontSolve ct
          (msg:cons) -> do
            let eq_ty = mkCoercionType Nominal msg ty2
                ev = mkProof "grit-only-if" ty1 ty2
            check_msg <- mkWanted (ctLoc ct) eq_ty
            check_cons <- mapM (mkWanted (ctLoc ct)) cons
            couldSolve (Just (ev, ct)) (check_msg:check_cons) Set.empty
          _ -> wontSolve ct
    _ -> wontSolve ct
  where unwrapOnlyIfs msg =
         case splitTyConApp_maybe msg of
           Just (tc, [con, msg]) | tc == ptc_only_if -> con : unwrapOnlyIfs msg
           _ -> [msg]

-- checkMsg generates a `m ~ Msg m0` constraint that we can solve, which unifies
-- the type variable m0 with whatever the resulting type error message is.
checkMsg :: PluginTyCons -> Ct -> Type -> TcPluginM (Ct, Type)
checkMsg PTC{..} ct msg =  do
  err_msg_kind <- flip mkTyConApp [] <$> getErrMsgCon
  ty_var <- mkTyVarTy <$> newFlexiTyVar err_msg_kind
  let eq_ty = mkCoercionType Nominal msg (mkTyConApp ptc_msg [ty_var])
  ct <- mkWanted (ctLoc ct) eq_ty
  ty_err <- mkTyErr ty_var
  return (ct, ty_err)

mkTyErr ::  Type -> TcPluginM Type
mkTyErr msg = flip mkTyConApp [typeKind msg, msg] <$>
                 tcLookupTyCon errorMessageTypeErrorFamName

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

postProcess _ _ env = do
   a <- liftIO $ readIORef $ tcg_static_wc env
   addedDyns <- addDyns (tcg_binds env)
   return env

addDyns :: LHsBinds GhcTc -> TcM (LHsBinds GhcTc)
addDyns = mapBagM addDynToBind
  where addDynToBind (L loc bind) = do
          liftIO $ putStrLn $ ((show $ toConstr bind) ++ ": "
                              ++ (showSDocUnsafe $ ppr bind))
          nb <- case bind of
                  AbsBinds {..} ->
                    do liftIO $ putStrLn $ (showSDocUnsafe $ ppr abs_ev_vars)
                       liftIO $ putStrLn $ (showSDocUnsafe $ ppr abs_tvs)
                       liftIO $ putStrLn $ (showSDocUnsafe $ ppr abs_ev_binds)
                       nds <- addDyns abs_binds
                       return (bind {abs_binds = nds})
                  FunBind {..} -> do
                    nfms <- addDynsToFun fun_matches
                    return (bind {fun_matches = nfms})
                  _ -> return bind
          return (L loc bind)

addDynsToFun :: MatchGroup GhcTc (LHsExpr GhcTc) -> TcM (MatchGroup GhcTc (LHsExpr GhcTc))
addDynsToFun (MG e (L l as) o) = do
    nas <- mapM addDynsToAlt as
    return (MG e (L l nas) o)
  where addDynsToAlt :: LMatch GhcTc (LHsExpr GhcTc) -> TcM (LMatch GhcTc (LHsExpr GhcTc))
        addDynsToAlt (L l (m@Match{..})) =  do
          nghrss <- addDynToGRHSs m_grhss
          return (L l (m {m_grhss = nghrss}))
        addDynToGRHSs :: GRHSs GhcTc (LHsExpr GhcTc) -> TcM (GRHSs GhcTc (LHsExpr GhcTc) )
        addDynToGRHSs (GRHSs e rhss (L l localbs)) = do
            nrhss <- mapM addDynToLGRHS rhss
            nlbs <- addDynToLBs localbs
            return (GRHSs e nrhss (L l nlbs))
        addDynToGRHSs x = return x
        addDynToLBs (HsValBinds x (ValBinds xvb bs sigs)) =
            do nbs <- addDyns bs
               return (HsValBinds x (ValBinds xvb nbs sigs))
        addDynToLBs x = return  x
        addDynToLGRHS (L l (GRHS x sts expr)) = do
            nexpr <- addDynToLHsExpr expr
            liftIO $ putStrLn $ showSDocUnsafe $ ppr sts
            return (L l (GRHS x sts nexpr))
        addDynToLGRHS x = return x
        addDynToLHsExpr (L l expr) = do
            nexpr <- addDynToExpr expr
            return (L l nexpr)
        addDynToLHsExpr (HSDo x ct (L l sts))
