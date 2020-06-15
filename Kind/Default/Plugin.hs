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
import Constraint
import ErrUtils (Severity(SevWarning))
import TcEvidence

import FamInstEnv

import TysPrim
import PrelNames
import Predicate
import TyCoRep

import ClsInst
import Class
import Inst hiding (newWanted)

import MkId
import TcMType (fillCoercionHole)
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
                        log_var :: Var, log_kind :: Kind,
                        log_res :: Type,
                        log_ct_flav :: CtFlavour}

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
   ppr LogDefault{..} = (case log_ct_flav of
                              Given -> text "Will default"
                              _ -> text "Defaulting")
                        -- We want to print a instead of a0
                        <+> quotes (ppr (mkTyVarTy log_var) <+> dcolon <+> ppr log_kind)
                        <+> text "to"
                        -- We want to print L instead of 'L if possible
                        <+> quotes (ppr log_res)
                        <+> text "in"
                        <+> quotes (ppr log_pred_ty)
                        <> text "!"

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
        ; let order = [ (solveReport,  "Reporting")
                      , (solveDefault, "Defaulting")
                      , (solveRelate,  "Relating")
                      , (solveIgnore,  "Ignoring")
                      , (solvePromote, "Promoting")]
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
                return $ PTC { ptc_default = ptc_default
                             , ptc_promote = ptc_promote
                             , ptc_ignore  = ptc_ignore
                             , ptc_relate  = ptc_relate
                             , ptc_report = ptc_report }
         NoPackage uid -> pprPanic "Plugin module not found (no package)!" (ppr uid)
         FoundMultiple ms -> pprPanic "Multiple plugin modules found!" (ppr ms)
         NotFound{..} -> pprPanic "Plugin module not found!" empty
  where getTyCon mod name = lookupOrig mod (mkTcOcc name) >>= tcLookupTyCon


type Solution = Either Ct (Maybe (EvTerm, Ct), -- The solution to the Ct
                           [Ct],               -- Possible additional work
                           [Log])              -- What we did



-- Defaults any ambiguous type variables of kind k to l if Default k = l
solveDefault :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveDefault _ famInsts PTC{..} ct | not (isCTyEqCan ct) =
   do (vars, defs) <- unzip . catMaybes <$> mapM getDefault (tyCoVarsOfCtList ct)
      if null vars
      then return $ Left ct
      else do let new_pred = substTyWith vars defs (ctPred ct)
                  new_co = mkUnivCo (PluginProv "sacred-defaulted") Nominal (ctPred ct) new_pred
                  predTy = mkPrimEqPredRole Nominal (ctPred ct) new_pred
              -- See [Note core-lint]
              (derived, logs) <- unzip <$> zipWithM mkTyEq vars defs
              return $ Right (Nothing,
                              map (flip setCtLoc loc . CNonCanonical) derived,
                              logs
                              )
   where tyVars = tyCoVarsOfCtList ct
         getDefault var =
           case lookupFamInstEnv famInsts ptc_default [varType var] of
             [FamInstMatch {fim_instance=FamInst{..}, ..}] ->
               do let rhs = fi_rhs
                      varTy = mkTyVarTy var
                      predTy = mkPrimEqPredRole Nominal varTy rhs
                  return (Just (var, rhs))
             _ -> return Nothing
         loc = ctLoc ct -- TODO: Should we bumpCtLocDepth here?
         mkTyEq var def = do let co = mkUnivCo (PluginProv "sacred-defaulted") Nominal
                                        (mkTyVarTy var) def
                                 predTy = mkPrimEqPredRole Nominal (mkTyVarTy var) def
                             nd <- newDerived loc predTy
                             return (nd, LogDefault{log_pred_ty = ctPred ct,
                                                    log_ct_flav = ctFlavour ct,
                                                    log_var = var,
                                                    log_kind = varType var,
                                                    log_res = def,
                                                    log_loc=loc} )

solveDefault _ _ _ ct = return $ Left ct

-- Solves con :: Constraint if Ignore con
solveIgnore :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveIgnore mode famInsts PTC{..} ct@CDictCan{cc_ev=cc_ev,
                                              cc_class=cls,
                                              cc_tyargs=tys,
                                              cc_pend_sc=psc} =
   case lookupFamInstEnv famInsts ptc_ignore [ctPred ct] of
      [] -> return $ Left ct
      _ | not (null $ classMethods cls) -> return $ Left ct -- We only do empty classes
      [FamInstMatch {fim_instance=fi@FamInst{fi_tys=fi_tys@(ignored:_),..}, ..}] ->
            do let new_rhs = substTyWith fi_tvs fim_tys fi_rhs
                   new_ev = cc_ev {ctev_pred = new_rhs}
               report <- newReport ptc_report (Log new_rhs (ctLoc ct))
               let cCon = tyConSingleDataCon (classTyCon cls)
               return $ Right (Just (evDataConApp cCon tys [], ct),
                               case mode of
                                 Defer -> [report]
                                 NoDefer -> [CNonCanonical {cc_ev=new_ev}],
                               [])
solveIgnore _ _ _ ct = return $ Left ct


-- Solves (a :: k) ~ (b :: k) if Relate k a b or Relate k b a
solveRelate :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveRelate mode famInsts PTC{..} ct =
   case splitTyConApp_maybe (ctPred ct) of
      Just (tyCon, [k1,k2,ty1,ty2]) | isEqPrimPred (ctPred ct)
                                      && k1 `eqType` k2 ->
            case  lookupFamInstEnv famInsts ptc_relate [k1, ty1, ty2]
               ++ lookupFamInstEnv famInsts ptc_relate [k1, ty2, ty1] of
               [] -> return $ Left ct
               (FamInstMatch {fim_instance=FamInst{..}, ..}:_) ->
                  do let new_rhs = substTyWith fi_tvs fim_tys fi_rhs
                         new_ev = (ctEvidence ct) {ctev_pred = new_rhs}
                     report <- newReport ptc_report (Log new_rhs (ctLoc ct))
                     return $ Right ( Just (mkProof "sacred-relateable" Nominal ty1 ty2, ct)
                                    , case mode of
                                        Defer -> [report]
                                        NoDefer -> [CNonCanonical {cc_ev =new_ev}]
                                    , [])
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
                    pty = case mode of
                             Defer -> mkTyConApp eqRep args
                             NoDefer -> new_rhs
                    new_ev = (ctEvidence ct) {ctev_pred = pty}
                report <- newReport ptc_report (Log new_rhs (ctLoc ct))
                return $ Right ( Just (mkProof "sacred-promoteable" Representational ty1 ty2, ct)
                               , case mode of
                                   Defer -> [report, CNonCanonical {cc_ev=new_ev}]
                                   NoDefer -> [CNonCanonical {cc_ev=new_ev}]
                               , [])
      _ -> return $ Left ct
  where eqRep = equalityTyCon Representational


-- Solve Report is our way of computing whatever type familes that might be in
-- a given type error before emitting it as a warning.
solveReport :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveReport _ _ PTC{..} ct = return $
   case splitTyConApp_maybe (ctPred ct) of
      Just r@(tyCon, [msg]) | getName tyCon == getName ptc_report ->
             let cCon = tyConSingleDataCon tyCon
             in Right (Just (evDataConApp cCon [msg] [], ct),
                   [], [Log msg (ctLoc ct)])
      _ -> Left ct

newReport :: TyCon -> Log -> TcPluginM Ct
newReport ptc_report Log{..} =
    do ev <- newWanted log_loc (mkTyConApp ptc_report [log_pred_ty])
       return $ setCtLoc CNonCanonical{cc_ev=ev} log_loc

-- Utils
mkProof :: String -> Role -> Type -> Type -> EvTerm
mkProof str role ty1 ty2 = evCoercion $ mkUnivCo (PluginProv str) role ty1 ty2

inspectSol :: [Either a (Maybe b, [c], [d])] -> ([a], ([b], [c], [d]))
inspectSol xs = (ls, (catMaybes sols, concat more, concat logs))
  where (ls, rs) = partitionEithers xs
        (sols, more, logs) = unzip3 rs
