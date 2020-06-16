-- Copyright (c) 2020 Matthías Páll Gissurarson
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE CPP #-}
module SACRED.Plugin ( plugin, module SACRED.Configure ) where

import SACRED.Configure

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
import TcType

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
plugin = defaultPlugin { tcPlugin = Just . sacredPlugin
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

data Mode = NoWarn | Defer | NoDefer deriving (Eq, Ord, Show)

getMode :: [CommandLineOption] -> Mode
getMode opts = if "defer" `elem` opts
               then if "no-warn" `elem` opts
                    then NoWarn else Defer
               else NoDefer

sacredPlugin :: [CommandLineOption] -> TcPlugin
sacredPlugin opts = TcPlugin initialize solve stop
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
              to_check = wanted ++ derived
        ; (_, (solved_wanteds, more_cts, logs)) <-
             foldM solveWFun (to_check, ([],[],[])) order
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
   do fpmRes <- findImportedModule (mkModuleName "SACRED.Configure") Nothing
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


wontSolve :: Ct -> TcPluginM Solution
wontSolve = return . Left

-- Defaults any ambiguous type variables of kind k to l if Default k = l
solveDefault :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveDefault mode famInsts PTC{..} ct
   | null defaults = wontSolve ct
   | otherwise =
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
      do assert_eqs <- mapM mkAssert eq_tys
         return $ Right (Nothing, assert_eqs, case mode of
                                                NoWarn -> []
                                                _ -> logs)
   where defaults = mapMaybe getDefault $ tyCoVarsOfCtList ct
         (eq_tys, logs) = unzip $ map mkTyEq defaults
         mkAssert :: Either PredType (Type, EvExpr) -> TcPluginM Ct
         mkAssert = either (mkDerived bump) (uncurry (mkGiven bump))
         bump = bumpCtLocDepth $ ctLoc ct
         getDefault var =
           case lookupFamInstEnv famInsts ptc_default [varType var] of
             [FamInstMatch{fim_instance=FamInst{..}}] -> Just (var, fi_rhs)
             _ -> Nothing
         mkTyEq (var,def) = ( if isMetaTyVar var
                              then Left pred_ty
                              else Right (pred_ty, proof),
                              LogDefault{log_pred_ty = ctPred ct,
                                         log_var = var, log_kind = varType var,
                                         log_res = def, log_loc =ctLoc ct})
           where EvExpr proof = mkProof "solve-defaultable" (mkTyVarTy var) def
                 pred_ty = mkPrimEqPredRole Nominal (mkTyVarTy var) def

-- Solves con :: Constraint if Ignore con
solveIgnore :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveIgnore mode famInsts PTC{..} ct@CDictCan{cc_ev=cc_ev, cc_class=cls,
                                              cc_tyargs=cls_tys} =
   case lookupFamInstEnv famInsts ptc_ignore [ctPred ct] of
      [] -> wontSolve ct
      _ | not (null $ classMethods cls) -> wontSolve ct -- We only do empty classes
      [FamInstMatch {fim_instance=FamInst{..},..}] ->
            do let new_rhs = substTyWith fi_tvs fim_tys fi_rhs
                   ty_err = CNonCanonical cc_ev{ctev_pred = new_rhs}
                   classCon = tyConSingleDataCon (classTyCon cls)
               report <- newReport ptc_report (Log new_rhs (ctLoc ct))
               return $ Right ( Just (evDataConApp classCon cls_tys [], ct)
                              ,  case mode of
                                   NoWarn -> []
                                   Defer -> [report]
                                   NoDefer -> [ty_err]
                              , [])
solveIgnore _ _ _ ct = wontSolve ct


-- Solves (a :: k) ~ (b :: k) if Relate k a b or Relate k b a
solveRelate :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveRelate mode famInsts PTC{..} ct =
  case splitTyConApp_maybe (ctPred ct) of
    Just (tyCon, [k1,k2,ty1,ty2]) | isEqPrimPred (ctPred ct)
                                    && k1 `eqType` k2 ->
      case lookupFamInstEnv famInsts ptc_relate [k1, ty1, ty2]
        ++ lookupFamInstEnv famInsts ptc_relate [k1, ty2, ty1] of
         [] -> wontSolve ct
         (FamInstMatch {fim_instance=FamInst{..}, ..}:_) ->
           do let new_rhs = substTyWith fi_tvs fim_tys fi_rhs
                  ty_err = CNonCanonical (ctEvidence ct) {ctev_pred = new_rhs}
              report <- newReport ptc_report (Log new_rhs (ctLoc ct))
              return $ Right (Just (mkProof "sacred-relateable" ty1 ty2, ct),
                              case mode of
                                NoWarn -> []
                                Defer -> [report]
                                NoDefer -> [ty_err],
                              [])
    _ -> wontSolve ct

-- Changes a ~ B c into Coercible a (B c) if Promote (B _)
solvePromote :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solvePromote mode famInsts PTC{..} ct =
   case splitTyConApp_maybe (ctPred ct) of
      Just r@(tyCon, args@[k1,k2,ty1,ty2]) | getUnique tyCon == eqPrimTyConKey
                                             && k1 `eqType` k2 ->
        case lookupFamInstEnv famInsts ptc_promote [ty1, ty2] of
           [] -> wontSolve ct
           [FamInstMatch {fim_instance=FamInst{..}, ..}] ->
             do let new_rhs = substTyWith fi_tvs fim_tys fi_rhs
                    eq_ty = mkPrimEqPredRole Representational ty1 ty2
                    ty_err  = CNonCanonical (ctEvidence ct){ctev_pred = new_rhs}
                check_coerce <- mkDerived (bumpCtLocDepth $ ctLoc ct) eq_ty
                report <- newReport ptc_report (Log new_rhs (ctLoc ct))
                return $ Right (Just (mkProof "sacred-promoteable" ty1 ty2, ct),
                                case mode of
                                  NoWarn -> [check_coerce]
                                  Defer -> [check_coerce, report]
                                  NoDefer -> [ty_err],
                                [])
      _ -> wontSolve ct


-- Solve Report is our way of computing whatever type familes that might be in
-- a given type error before emitting it as a warning.
solveReport :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveReport _ _ PTC{..} ct =
   case splitTyConApp_maybe (ctPred ct) of
      Just r@(tyCon, [msg]) | getName tyCon == getName ptc_report ->
        return $ Right ( Just (evDataConApp (tyConSingleDataCon tyCon) [msg] [], ct),
                        [], [Log msg (ctLoc ct)])
      _ -> wontSolve ct

-- Utils
mkDerived :: CtLoc -> PredType -> TcPluginM Ct
mkDerived loc eq_ty = flip setCtLoc loc . CNonCanonical <$> newDerived loc eq_ty

mkGiven :: CtLoc -> PredType -> EvExpr -> TcPluginM Ct
mkGiven loc eq_ty ev = flip setCtLoc loc . CNonCanonical
                         <$> newGiven loc eq_ty ev

newReport :: TyCon -> Log -> TcPluginM Ct
newReport ptc_report Log{..} =
    do ev <- newWanted log_loc (mkTyConApp ptc_report [log_pred_ty])
       return $ setCtLoc CNonCanonical{cc_ev=ev} log_loc

mkProof :: String -> Type -> Type -> EvTerm
mkProof str ty1 ty2 = evCoercion $ mkUnivCo (PluginProv str) Nominal ty1 ty2

inspectSol :: [Either a (Maybe b, [c], [d])] -> ([a], ([b], [c], [d]))
inspectSol xs = (ls, (catMaybes sols, concat more, concat logs))
  where (ls, rs) = partitionEithers xs
        (sols, more, logs) = unzip3 rs
