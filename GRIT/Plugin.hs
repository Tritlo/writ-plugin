-- Copyright (c) 2020 Matthías Páll Gissurarson
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE CPP #-}
module GRIT.Plugin ( plugin, module GRIT.Configure ) where

import GRIT.Configure

import Control.Monad (when, guard, foldM, zipWithM, msum)
import Data.Maybe (mapMaybe, catMaybes, fromMaybe, fromJust, listToMaybe, isJust)
import Data.Either
import Data.IORef
import Data.List (nub, sort)
import Data.Function (on)
import Data.Kind (Constraint)
import Data.Data (Data, toConstr)
import Prelude hiding ((<>))

import GHC.TypeLits(TypeError(..), ErrorMessage(..))

#if __GLASGOW_HASKELL__ > 810
import GHC.Plugins hiding (TcPlugin)
import GHC.Tc.Plugin

import GHC.Tc.Types
import GHC.Tc.Types.Evidence
import GHC.Tc.Types.Constraint
import GHC.Tc.Utils.TcMType (fillCoercionHole)


import GHC.Core.TyCo.Rep
import GHC.Core.Predicate
import GHC.Core.Class

import GHC.Utils.Error

import GHC.Builtin.Types.Prim
import GHC.Builtin.Names

import GHC.Types.Id.Make
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
import TcMType (fillCoercionHole)

import TcType
import CoAxiom
import Unify

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
                       , pluginRecompile = purePlugin }


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
           _ -> text "GRIT" <+> ppr log_pred_ty
   ppr LogDefault{..} = text "Defaulting"
                        -- We want to print a instead of a0
                        <+> quotes (ppr (mkTyVarTy log_var)
                                   <+> dcolon <+> ppr log_kind)
                        <+> text "to"
                        -- We want to print L instead of 'L if possible
                        <+> quotes (ppr log_res)
                        <+> text "in"
                        <+> quotes (ppr log_pred_ty)
                        <> text "!"
      where printFlav Given = "Will default"
            printFlav _ = "Defaulting"

addWarning :: DynFlags -> Log -> IO()
addWarning dflags log = warn (ppr log)
  where warn = putLogMsg dflags NoReason SevWarning
#if __GLASGOW_HASKELL__ > 810
                 (RealSrcSpan (logSrc log) Nothing)
#else
                 (RealSrcSpan (logSrc log)) (defaultErrStyle dflags)
#endif

data Flags = Flags { f_debug        :: Bool
                   , f_quiet        :: Bool
                   , f_no_ignore    :: Bool
                   , f_no_promote   :: Bool
                   , f_no_default   :: Bool
                   , f_keep_errors  :: Bool
                   , f_no_discharge :: Bool }

getFlags :: [CommandLineOption] -> Flags
getFlags opts = Flags { f_debug        = "debug"          `elem` opts
                      , f_quiet        = "quiet"          `elem` opts
                      , f_no_ignore    = "no-ignore"      `elem` opts
                      , f_no_promote   = "no-promote"     `elem` opts
                      , f_no_default   = "no-default"     `elem` opts
                      , f_keep_errors  = "keep-errors"    `elem` opts 
                      , f_no_discharge = "no-discharge"   `elem` opts }

gritPlugin :: [CommandLineOption] -> TcPlugin
gritPlugin opts = TcPlugin initialize solve stop
  where
     flags@Flags{..} = getFlags opts
     initialize = tcPluginIO $ newIORef []
     solve :: IORef [Log] -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
     solve warns given derived wanted = do {
        ; dflags <- unsafeTcPluginTcM getDynFlags
        ; let pprDebug :: Outputable a => String -> a -> TcPluginM ()
              pprDebug str a =
                when f_debug $
                  tcPluginIO $ putStrLn (str ++ " " ++ showSDoc dflags (ppr a))
        ; pprDebug "Solving" empty
        ; mapM_ (pprDebug "Given:") given
        ; mapM_ (pprDebug "Derived:") derived
        ; mapM_ (pprDebug "Wanted:") wanted
        ; pluginTyCons <- getPluginTyCons
        ; let solveWFun (unsolved, (solved, more, logs)) (solveFun, explain) =
                do  {(still_unsolved, (new_solved, new_more, new_logs)) <-
                         inspectSol <$>
                            mapM (solveFun flags pluginTyCons) unsolved
                    ; mapM_ (pprDebug (explain ++ "-sols")) new_solved
                    ; mapM_ (pprDebug (explain ++ "-more")) new_more
                    ; mapM_ (pprDebug (explain ++ "-reps") . pprRep) new_more
                    ; mapM_ (pprDebug (explain ++ "-logs")) new_logs
                    ; return (still_unsolved, (solved ++ new_solved,
                                               more ++ new_more,
                                               logs ++ new_logs)) }
        ; let order = [ (solveReport,    "Reporting")
                      , (solveDefault,   "Defaulting")
                      , (solveDischarge, "Discharging")
                      , (solveIgnore,    "Ignoring")
                      , (solvePromote,   "Promoting") ]
              to_check = wanted ++ derived
        ; mapM_ (pprDebug "Checking" . pprRep) to_check
        ; (_, (solved_wanteds, more_cts, logs)) <-
             foldM solveWFun (to_check, ([],[],[])) order
        ; tcPluginIO $ modifyIORef warns (logs ++)
        ; return $ TcPluginOk solved_wanteds more_cts }
     stop warns =
        do { dflags <- unsafeTcPluginTcM getDynFlags
           ; tcPluginIO $ readIORef warns >>= mapM_ (addWarning dflags) . sort . nub }

data PluginTyCons = PTC { ptc_default :: TyCon
                        , ptc_promote :: TyCon
                        , ptc_only_if :: TyCon
                        , ptc_ignore  :: TyCon
                        , ptc_discharge  :: TyCon
                        , ptc_report  :: TyCon }

getPluginTyCons :: TcPluginM PluginTyCons
getPluginTyCons =
   do fpmRes <- findImportedModule (mkModuleName "GRIT.Configure") Nothing
      case fpmRes of
         Found _ mod  ->
             do ptc_default <- getTyCon mod "Default"
                ptc_discharge  <- getTyCon mod "Discharge"
                ptc_promote <- getTyCon mod "Promote"
                ptc_ignore  <- getTyCon mod "Ignore"
                ptc_report  <- getTyCon mod "Report"
                ptc_only_if <- getTyCon mod "OnlyIf"
                return PTC{..}
         NoPackage uid -> pprPanic "Plugin module not found (no package)!" (ppr uid)
         FoundMultiple ms -> pprPanic "Multiple plugin modules found!" (ppr ms)
         NotFound{..} -> pprPanic "Plugin module not found!" empty
  where getTyCon mod name = lookupOrig mod (mkTcOcc name) >>= tcLookupTyCon


type Solution = Either Ct (Maybe (EvTerm, Ct), -- The solution to the Ct
                           [Ct],               -- Possible additional work
                           [Log])              -- What we did


wontSolve :: Ct -> TcPluginM Solution
wontSolve = return . Left

pprRep :: Ct -> SDoc
pprRep ct =
  case userTypeError_maybe (ctPred ct) of
     Just m -> pprUserTypeErrorTy m <+> ppr (ctLocSpan $ ctLoc ct)
     _ -> case splitTyConApp_maybe (ctPred ct) of
            Just (tc, [msg]) -> pprUserTypeErrorTy msg <+> ppr (ctLocSpan $ ctLoc ct)
            _ -> pprUserTypeErrorTy (ctPred ct) <+> ppr (ctLocSpan $ ctLoc ct)


-- Defaults any ambiguous type variables of kind k to l if Default k = l
solveDefault :: Flags -> PluginTyCons -> Ct -> TcPluginM Solution
solveDefault Flags{..} _ ct | f_no_default = wontSolve ct
solveDefault Flags{..} ptc@PTC{..} ct =
  do defaults <- catMaybes <$> mapM getDefault (tyCoVarsOfCtList ct)
     if null defaults
     then wontSolve ct
     else
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
      do let (eq_tys, logs) = unzip $ map mkTyEq defaults
         assert_eqs <- mapM mkAssert eq_tys
         return $ Right ( Nothing
                        , assert_eqs
                        , if f_quiet then [] else logs)
   where mkAssert :: Either PredType (Type, EvExpr) -> TcPluginM Ct
         mkAssert = either (mkDerived bump) (uncurry (mkGiven bump))
         bump = bumpCtLocDepth $ ctLoc ct
         getDefault var = do
           res <- matchFam ptc_default [varType var]
           case res of
             Just (_, rhs) -> return $ Just (var, rhs)
             _ -> return Nothing
         mkTyEq (var,def) = ( if isMetaTyVar var
                              then Left pred_ty
                              else Right (pred_ty, proof),
                              LogDefault{log_pred_ty = ctPred ct,
                                         log_var = var, log_kind = varType var,
                                         log_res = def, log_loc =ctLoc ct})
           where EvExpr proof = mkProof "solve-defaultable" (mkTyVarTy var) def
                 pred_ty = mkPrimEqPredRole Nominal (mkTyVarTy var) def

-- Solves con :: Constraint if Ignore con
solveIgnore :: Flags -> PluginTyCons -> Ct -> TcPluginM Solution
solveIgnore Flags{..} _ ct | f_no_ignore = wontSolve ct
solveIgnore _ _ ct@CDictCan{..} | not (null $ classMethods cc_class) = wontSolve ct
solveIgnore Flags{..} ptc@PTC{..} ct@CDictCan{..} = do
  res <- matchFam ptc_ignore [ctPred ct]
  case res of
    Nothing -> wontSolve ct
    Just (_, rhs) ->
       do let ty_err = newTyErr ct rhs
              classCon = tyConSingleDataCon (classTyCon cc_class)
          report <- newReport ptc_report ct rhs
          additional_constraints <- additionalConstraints ptc (ctLoc ct) rhs
          return $ Right ( Just (evDataConApp classCon cc_tyargs [], ct)
                         , if f_keep_errors then [ty_err]
                           else report:additional_constraints
                         , [])
solveIgnore _ _ ct = wontSolve ct


-- Solves (a :: k) ~ (b :: k) if Discharge k a b or Discharge k b a
solveDischarge :: Flags -> PluginTyCons -> Ct -> TcPluginM Solution
solveDischarge Flags{..} _ ct | f_no_discharge = wontSolve ct
solveDischarge Flags{..} ptc@PTC{..} ct =
  case splitTyConApp_maybe (ctPred ct) of
    Just (tyCon, [k1,k2,ty1,ty2]) | isEqPrimPred (ctPred ct) ->
      do res <- matchFam ptc_discharge [k1,ty1,ty2]
         case res of
           Nothing -> wontSolve ct
           Just (_, rhs) -> do
            let ty_err = newTyErr ct rhs
            report <- newReport ptc_report ct rhs
            additional_constraints <- additionalConstraints ptc (ctLoc ct) rhs
            return $ Right (Just (mkProof "grit-dischargeable" ty1 ty2, ct)
                          , if f_keep_errors then [ty_err]
                            else report:additional_constraints
                          , [])
    _ -> wontSolve ct

-- Changes a ~ B c into Coercible a (B c) if Promote (B _)
solvePromote :: Flags -> PluginTyCons -> Ct -> TcPluginM Solution
solvePromote Flags{..} _  ct  | f_no_promote = wontSolve ct
solvePromote Flags{..} ptc@PTC{..} ct =
   case splitTyConApp_maybe (ctPred ct) of
      Just r@(tyCon, args@[k1,k2,ty1,ty2]) | getUnique tyCon == eqPrimTyConKey
                                             && k1 `eqType` k2 -> do
       res <- matchFam ptc_promote [ty1, ty2]
       case res of
         Just (_, rhs) -> do
            let ty_err = newTyErr ct rhs
                eq_ty = mkPrimEqPredRole Representational ty1 ty2
            report <- newReport ptc_report ct rhs
            check_coerce <- mkWanted (bumpCtLocDepth $ ctLoc ct) eq_ty
            additional_constraints <- additionalConstraints ptc (ctLoc ct) rhs
            return $ Right (Just (mkProof "grit-promoteable" ty1 ty2, ct)
                           , if f_keep_errors then [ty_err]
                            else [check_coerce, report] ++ additional_constraints
                           , [])
         _ -> wontSolve ct
      _ -> wontSolve ct

-- Additional constraints allow users to specify additional constraints for
-- promotions and discharges.
additionalConstraints :: PluginTyCons -> CtLoc -> Type -> TcPluginM [Ct]
additionalConstraints PTC{..} loc ty =
  case splitTyConApp_maybe ty of
    Just (tc, constraint:_) | tc == ptc_only_if ->
      pure <$> mkWanted (bumpCtLocDepth loc) constraint
    _ -> return []

-- Solve Report is our way of computing whatever type familes that might be in
-- a given type error before emitting it as a warning or error depending on
-- which flags are set.
solveReport :: Flags -> PluginTyCons -> Ct -> TcPluginM Solution
solveReport Flags{..} PTC{..} ct =
   case splitTyConApp_maybe (ctPred ct) of
      Just r@(tyCon, [msg]) | getName tyCon == getName ptc_report -> do
        let ev = Just (evDataConApp (tyConSingleDataCon tyCon) [msg] [], ct)
        Right <$>
         case tryImproveTyErr msg of
           Just imp -> do report <- newReport ptc_report ct imp
                          return (ev, [report], [])
           _ -> if f_quiet
                then return (ev, [], [])
                else return (ev, [], [Log msg (ctLoc ct)])
      _ -> wontSolve ct

-- tryImproveTyErr goes over a type error type and tries to fully apply all
-- closed type families. This is to prevent things like 'LabelPpr a' from
-- showing up in the error message if there is a  'default' case for LabelPpr a.
tryImproveTyErr :: Type -> Maybe Type
tryImproveTyErr msg =
  do (tc, _k:msg:rest) <- splitTyConApp_maybe msg
     guard (tyConName tc == errorMessageTypeErrorFamName)
     imp <- improve' msg
     return $ mkTyConApp tc (_k:imp:rest)
  where
    splitTcs = [typeErrorAppendDataConName, typeErrorVAppendDataConName]
    improve' :: Type -> Maybe Type
    improve' arg = do
       (tc, args) <- splitTyConApp_maybe arg
       let name = tyConName tc
       guard (name `notElem` [typeErrorTextDataConName, typeErrorShowTypeDataConName])
       if name `elem` splitTcs
       then let [t1, t2] = args
            in mkTyConApp tc <$> case (improve' t1, improve' t2) of
                                   (Just it1, Just it2) -> Just [it1, it2]
                                   (Just it1, _) -> Just [it1,t2]
                                   (_, Just it2) -> Just [t1,it2]
                                   _ -> Nothing
       else do tryEval arg
    -- Try eval uses the "default" case of a type family, in case not all the
    -- parameters are known. Essentially the type family without the apartness
    -- check. It is only used to improve the message for reports.
    tryEval :: Type -> Maybe Type
    tryEval arg = do
        (tc, args) <- splitTyConApp_maybe arg
        ax <- isClosedSynFamilyTyConWithAxiom_maybe tc
        let branches = fromBranches $ co_ax_branches ax
        listToMaybe $ mapMaybe (getMatches args) branches
    getMatches :: [Type] -> CoAxBranch -> Maybe Type
    getMatches args CoAxBranch{..}
      = do subst <- tcMatchTys cab_lhs args
           return $ substTyWith cab_tvs (substTyVars subst cab_tvs) cab_rhs

-- Utils
mkDerived :: CtLoc -> PredType -> TcPluginM Ct
mkDerived loc eq_ty = flip setCtLoc loc . CNonCanonical <$> newDerived loc eq_ty

mkWanted :: CtLoc -> PredType -> TcPluginM Ct
mkWanted loc eq_ty = flip setCtLoc loc . CNonCanonical <$> newWanted loc eq_ty

mkGiven :: CtLoc -> PredType -> EvExpr -> TcPluginM Ct
mkGiven loc eq_ty ev = flip setCtLoc loc . CNonCanonical <$> newGiven loc eq_ty ev

newReport :: TyCon -> Ct -> PredType -> TcPluginM Ct
newReport ptc_report ct msg =
 flip setCtLoc (ctLoc ct) . CNonCanonical <$> newWanted (ctLoc ct) rep
  where rep = mkTyConApp ptc_report [msg]

newTyErr :: Ct -> PredType -> Ct
newTyErr ct msg = CNonCanonical (ctEvidence ct){ctev_pred=msg}

mkProof :: String -> Type -> Type -> EvTerm
mkProof str ty1 ty2 = evCoercion $ mkUnivCo (PluginProv str) Nominal ty1 ty2

inspectSol :: [Either a (Maybe b, [c], [d])] -> ([a], ([b], [c], [d]))
inspectSol xs = (ls, (catMaybes sols, concat more, concat logs))
  where (ls, rs) = partitionEithers xs
        (sols, more, logs) = unzip3 rs
