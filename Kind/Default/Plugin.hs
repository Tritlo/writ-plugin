-- Copyright (c) 2020 Matthías Páll Gissurarson
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE CPP #-}
module Kind.Default.Plugin ( plugin, module Kind.Default) where

import Kind.Default

import Control.Monad (when, guard, foldM, zipWithM)
import Data.Maybe (mapMaybe, catMaybes, fromMaybe, fromJust)
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


import GHC.Core.FamInstEnv
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

import FamInstEnv

import TysPrim
import PrelNames
import TyCoRep

import ClsInst
import Class
import Inst hiding (newWanted)

import MkId
import TcMType (fillCoercionHole)

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
plugin = defaultPlugin { tcPlugin = Just . kindDefaultPlugin
                       , pluginRecompile = purePlugin }

{- [Note core-lint]
 - NOTE: core-lint is not very good with weird equalities. Notably,
 - we hit this bug: https://gitlab.haskell.org/ghc/ghc/issues/16246.
 - I don't think it's an issue though.
 -}

-------------------------------------------------------------------------------
data Log = Log { log_pred_ty :: Type, log_loc :: CtLoc}
         | LogDefault { log_pred_ty :: Type, log_loc :: CtLoc,
                        log_var :: Var, log_kind :: Kind, log_res :: Type }

logSrc :: Log -> RealSrcSpan
logSrc = ctLocSpan . log_loc

instance Ord Log where
  compare Log{} LogDefault{}  = GT
  compare LogDefault{} Log{}  = LT
  compare a b = compare (logSrc a) (logSrc b)

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
           _ -> text "SACRED" <+> ppr log_pred_ty
   ppr LogDefault{..} = text "Defaulting"
                        -- We want to print a instead of a0
                        <+> quotes (ppr (mkTyVarTy log_var) <+> dcolon <+> ppr log_kind)
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
#if __GLASGOW_HASKELL__ > 810
  where warn = putLogMsg dflags NoReason SevWarning (RealSrcSpan (logSrc log) Nothing)
#else
  where warn = putLogMsg dflags NoReason SevWarning (RealSrcSpan (logSrc log)) (defaultErrStyle dflags)
#endif

data Mode = Defer | NoDefer deriving (Eq, Ord, Show)

getMode :: [CommandLineOption] -> Mode
getMode opts = if "defer" `elem` opts then Defer else NoDefer

kindDefaultPlugin :: [CommandLineOption] -> TcPlugin
kindDefaultPlugin opts = TcPlugin initialize solve stop
  where
     debug = "debug" `elem` opts
     mode = getMode opts
     initialize = tcPluginIO $ newIORef []
     solve :: IORef [Log] -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
     solve warns given derived wanted = do {
        ; dflags <- unsafeTcPluginTcM getDynFlags
        ; let pprDebug :: Outputable a => String -> a -> TcPluginM ()
              pprDebug str a =
                when debug $
                  tcPluginIO $ putStrLn (str ++ " " ++ showSDoc dflags (ppr a))
        ; pprDebug "Solving" empty
        ; mapM_ (pprDebug "Given:") given
        ; mapM_ (pprDebug "Given:" . map varType . tyCoVarsOfCtList ) given
        ; mapM_ (pprDebug "Derived:") derived
        ; mapM_ (pprDebug "Wanted:") wanted
        ; instEnvs <- getFamInstEnvs
        ; pluginTyCons <- getPluginTyCons

        ; let solveWFun (unsolved, (solved, more, logs)) (solveFun, explain) =
                do  {(still_unsolved, (new_solved, new_more, new_logs)) <-
                         inspectSol <$>
                            mapM (solveFun mode instEnvs pluginTyCons) unsolved
                    ; mapM_ (pprDebug (explain ++ "-sols")) new_solved
                    ; mapM_ (pprDebug (explain ++ "-more")) new_more
                    ; mapM_ (pprDebug (explain ++ "-logs")) new_logs
                    ; return (still_unsolved, (solved ++ new_solved,
                                               more ++ new_more,
                                               logs ++ new_logs)) }
        ; let order = [(solveReport,  "Reporting"), (solveDefault, "Defaulting")
                      ,(solveRelate,  "Relating"),  (solveIgnore,  "Ignoring")
                      ,(solvePromote, "Promoting")]
        ; (_, (solved_wanteds, more_cts, logs)) <-
             foldM solveWFun (wanted, ([],[],[])) order
        ; tcPluginIO $ modifyIORef warns (logs ++)
        ; return $ TcPluginOk solved_wanteds more_cts }
     stop warns =
        do { dflags <- unsafeTcPluginTcM getDynFlags
           ; tcPluginIO $ readIORef warns >>= mapM_ (addWarning dflags) . sort . nub }

data PluginTyCons = PTC { ptc_default :: TyCon
                        , ptc_promote :: TyCon
                        , ptc_ignore  :: TyCon
                        , ptc_relate  :: TyCon
                        , ptc_report  :: TyCon }

getPluginTyCons :: TcPluginM PluginTyCons
getPluginTyCons =
   do fpmRes <- findImportedModule (mkModuleName "Kind.Default") Nothing
      case fpmRes of
         Found _ mod  ->
             do ptc_default <- getTyCon mod "Default"
                ptc_relate  <- getTyCon mod "Relate"
                ptc_promote <- getTyCon mod "Promote"
                ptc_ignore  <- getTyCon mod "Ignore"
                ptc_report  <- getTyCon mod "Report"
                return PTC{..}
         NoPackage uid -> pprPanic "Plugin module not found (no package)!" (ppr uid)
         FoundMultiple ms -> pprPanic "Multiple plugin modules found!" (ppr ms)
         NotFound{..} -> pprPanic "Plugin module not found!" empty
  where getTyCon mod name = lookupOrig mod (mkTcOcc name) >>= tcLookupTyCon


type Solution = Either Ct (Maybe (EvTerm, Ct), -- The solution to the Ct
                           [Ct],               -- Possible additional work
                           [Log])              -- What we did



-- Defaults any ambiguous type variables of kind k to l if Default k = l
solveDefault :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveDefault _ famInsts PTC{..} ct | null defaults = return $ Left ct
                                   | otherwise =
      -- We make assertions that a ~ def for all free a in pred_ty of ct.
      do assert_eqs <- mapM (mkAssert (ctLoc ct)) eq_tys
         return $ Right (Nothing, assert_eqs, logs)
   where defaults = mapMaybe getDefault (tyCoVarsOfCtList ct)
         (eq_tys, logs) = unzip $ map mkTyEq defaults
         getDefault var =
           case lookupFamInstEnv famInsts ptc_default [varType var] of
             [FamInstMatch{fim_instance=FamInst{..}}] -> Just (var, fi_rhs)
             _ -> Nothing
         mkTyEq (var,def) = (mkPrimEqPredRole Nominal (mkTyVarTy var) def,
                             LogDefault{log_pred_ty = ctPred ct,
                                        log_var = var, log_kind = varType var,
                                        log_res = def, log_loc =ctLoc ct})

-- Solves con :: Constraint if Ignore con
solveIgnore :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveIgnore mode famInsts PTC{..} ct@CDictCan{cc_ev=cc_ev, cc_class=cls,
                                              cc_tyargs=cls_tys} =
   case lookupFamInstEnv famInsts ptc_ignore [ctPred ct] of
      [] -> return $ Left ct
      _ | not (null $ classMethods cls) -> return $ Left ct -- We only do empty classes
      [FamInstMatch {fim_instance=FamInst{..},..}] ->
            do let new_rhs = substTyWith fi_tvs fim_tys fi_rhs
                   ty_err = CNonCanonical cc_ev{ctev_pred = new_rhs}
                   classCon = tyConSingleDataCon (classTyCon cls)
               report <- newReport ptc_report (Log new_rhs (ctLoc ct))
               return $ Right ( Just (evDataConApp classCon cls_tys [], ct)
                              ,  case mode of
                                   Defer -> [report]
                                   NoDefer -> [ty_err]
                              , [])
solveIgnore _ _ _ ct = return $ Left ct


-- Solves (a :: k) ~ (b :: k) if Relate k a b or Relate k b a
solveRelate :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveRelate mode famInsts PTC{..} ct =
   case splitTyConApp_maybe (ctPred ct) of
      Just (tyCon, [k1,k2,ty1,ty2]) | isEqPrimPred (ctPred ct)
                                      && k1 `eqType` k2 ->
        case lookupFamInstEnv famInsts ptc_relate [k1, ty1, ty2]
          ++ lookupFamInstEnv famInsts ptc_relate [k1, ty2, ty1] of
           [] -> return $ Left ct
           (FamInstMatch {fim_instance=FamInst{..}, ..}:_) ->
             do let new_rhs = substTyWith fi_tvs fim_tys fi_rhs
                    ty_err = CNonCanonical (ctEvidence ct) {ctev_pred = new_rhs}
                report <- newReport ptc_report (Log new_rhs (ctLoc ct))
                return $ Right (Just (mkProof "sacred-relateable" Nominal ty1 ty2, ct),
                                case mode of
                                  Defer -> [report]
                                  NoDefer -> [ty_err],
                                [])
      _ -> return $ Left ct

-- Changes a ~ B c into Coercible a (B c) if Promote (B _)
solvePromote :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solvePromote mode famInsts PTC{..} ct =
   case splitTyConApp_maybe (ctPred ct) of
      Just r@(tyCon, args@[k1,k2,ty1,ty2]) | getUnique tyCon == eqPrimTyConKey
                                             && k1 `eqType` k2 ->
        case lookupFamInstEnv famInsts ptc_promote [ty1, ty2] of
           [] -> return $ Left ct
           [FamInstMatch {fim_instance=FamInst{..}, ..}] ->
             do let new_rhs = substTyWith fi_tvs fim_tys fi_rhs
                    eq_ty = mkPrimEqPredRole Representational ty1 ty2
                    ty_err  = CNonCanonical (ctEvidence ct){ctev_pred = new_rhs}
                check_coerce <- mkAssert (ctLoc ct) eq_ty
                report <- newReport ptc_report (Log new_rhs (ctLoc ct))
                return $ Right (Just (mkProof "sacred-promoteable" Nominal ty1 ty2, ct),
                                case mode of
                                  Defer -> [report, check_coerce]
                                  NoDefer -> [ty_err],
                                [])
      _ -> return $ Left ct



-- Solve Report is our way of computing whatever type familes that might be in
-- a given type error before emitting it as a warning.
solveReport :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveReport _ _ PTC{..} ct = return $
   case splitTyConApp_maybe (ctPred ct) of
      Just r@(tyCon, [msg]) | getName tyCon == getName ptc_report ->
        Right (Just (evDataConApp (tyConSingleDataCon tyCon) [msg] [], ct),
               [], [Log msg (ctLoc ct)])
      _ -> Left ct

-- Utils
mkAssert :: CtLoc -> PredType -> TcPluginM Ct
mkAssert loc eq_ty = flip setCtLoc loc . CNonCanonical <$> newDerived loc eq_ty

newReport :: TyCon -> Log -> TcPluginM Ct
newReport ptc_report Log{..} =
    do ev <- newWanted log_loc (mkTyConApp ptc_report [log_pred_ty])
       return $ setCtLoc CNonCanonical{cc_ev=ev} log_loc

mkProof :: String -> Role -> Type -> Type -> EvTerm
mkProof str role ty1 ty2 = evCoercion $ mkUnivCo (PluginProv str) role ty1 ty2

inspectSol :: [Either a (Maybe b, [c], [d])] -> ([a], ([b], [c], [d]))
inspectSol xs = (ls, (catMaybes sols, concat more, concat logs))
  where (ls, rs) = partitionEithers xs
        (sols, more, logs) = unzip3 rs
