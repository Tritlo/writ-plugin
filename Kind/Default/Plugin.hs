-- Copyright (c) 2020 Matthías Páll Gissurarson
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
module Kind.Default.Plugin ( plugin, module Kind.Default) where

import Kind.Default
import GhcPlugins hiding (TcPlugin)
import TcRnTypes
import TcPluginM
import Constraint 
import ErrUtils (Severity(SevWarning))
import TcEvidence --(EvTerm (..), evCoercion)

import Control.Monad (when, guard, foldM)
import Data.Maybe (mapMaybe, catMaybes, fromMaybe, fromJust)
import Data.Either
import Data.IORef
import Data.List (nub, sort)
import Data.Function (on)

import FamInstEnv

import TysPrim (equalityTyCon)
import PrelNames (eqPrimTyConKey)
import Predicate (EqRel(NomEq), isEqPrimPred, predTypeEqRel)
import TyCoRep (UnivCoProvenance(..), mkTyCoVarTy)
import Data.Kind (Constraint)
import Data.Data (Data, toConstr)

import GHC.TypeLits(TypeError(..), ErrorMessage(..))
import GHC.Hs
--import MkCore
--import TcHsSyn (zonkTcTypeToType)
import ClsInst
import Class
import Inst (newClsInst)

import MkId (mkDictFunId)

--------------------------------------------------------------------------------
-- Exported

plugin :: Plugin
plugin = defaultPlugin { tcPlugin = Just . kindDefaultPlugin
                       , pluginRecompile = purePlugin }

-------------------------------------------------------------------------------
data Log = Log Type CtFlavour CtLoc

logSrc :: Log -> RealSrcSpan
logSrc (Log _ _ l) = ctLocSpan l

logTy :: Log -> Type
logTy (Log t _ _) = t

instance Ord Log where
  compare = compare `on` logSrc

instance Eq Log where
   logA == logB =
       (((==) `on` logSrc) logA logB) && ((eqType `on` logTy) logA logB)

instance Outputable Log where
   -- We do some extra work to pretty print the Defaulting messages
   ppr (Log ty flav _) =
        case userTypeError_maybe ty of
           Just msg -> pprUserTypeErrorTy msg
           _ ->  case splitTyConApp_maybe ty of
                   Just (tc, [k1,k2,ty1,ty2]) | isEqPrimPred ty ->
                                               -- && isTyVarTy ty1 ->
                        (case flav of
                           Given -> text "Will default"
                           _ -> text "Defaulting")
                        -- We want to print a instead of a0
                        <+> quotes (if isTyVarTy ty1
                                     then ppr
                                        (occName $ getTyVar "" ty1) <+> dcolon <+> ppr k1
                                     else ppr ty1)
                        <+> text "to"
                        -- We want to print L instead of 'L if possible
                        <+> quotes ( case (do (tc, []) <- splitTyConApp_maybe ty2
                                              isPromotedDataCon_maybe tc) of
                                        Just dc -> ppr dc
                                        _ -> ppr ty2)
                   _ -> text "SACRED" <+> ppr ty

addWarning :: DynFlags -> Log -> IO()
addWarning dflags log = warn (ppr log)
  where warn = putLogMsg dflags NoReason SevWarning
                         (RealSrcSpan $ logSrc log)
                         (defaultErrStyle dflags)

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

        ; (_, (_, more_givens, given_logs)) <-
             foldM solveWFun (given, ([],[],[])) [(solveWarnDefault, "Defaulting")]
        -- NOTE: core-lint is not very good with weird equalities. Notably,
        -- it lints acoercion, and then tries to remake it using
        -- "mkHeteroCoercionType", which is not the right thing to do. I belive
        -- it has been fixed in 8.12, at least "mkHetreoCoercionType" isn't
        -- used anywhere for linting.
        ; (_, (solved_wanteds, more_cts, logs)) <-
             foldM solveWFun (wanted, ([],more_givens,given_logs)) [ (solveReport, "Reporting")
                                                                   , (solveDefault, "Defaulting")
                                                                   , (solveRelate,  "Relating")
                                                                   , (solveIgnore,  "Ignoring")
                                                                   , (solvePromote, "Promoting") ]
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
                  new_co = mkUnivCo (PluginProv "Defaulted") Nominal (ctPred ct) new_pred
                  predTy = mkPrimEqPredRole Nominal (ctPred ct) new_pred
              -- TODO: Should we be outputting derived here? Can cause us to
              -- hit this bug: https://gitlab.haskell.org/ghc/ghc/issues/16246
              new_g <- newGiven (bumpCtLocDepth $ ctLoc ct) predTy (Coercion new_co)
              --new_w <- newDerived (bumpCtLocDepth $ ctLoc ct) predTy
              return $ Right (Nothing,--Just (evCoercion new_co,ct),
                              map (flip setCtLoc (ctLoc ct) . CNonCanonical)
                                    [new_g],
                              [Log predTy (ctFlavour ct) (ctLoc ct)])
   where tyVars = tyCoVarsOfCtList ct
         getDefault var =
           case lookupFamInstEnv famInsts ptc_default [varType var] of
             [FamInstMatch {fim_instance=FamInst{..}, ..}] ->
               do let rhs = fi_rhs
                      varTy = mkTyVarTy var
                      predTy = mkPrimEqPredRole Nominal varTy rhs
                  return (Just (var, rhs))
             _ -> return Nothing
solveDefault _ _ _ ct = return $ Left ct


solveWarnDefault :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveWarnDefault _ famInsts PTC{..} ct | not (isCTyEqCan ct) && isGivenCt ct  =
   return $ Right (Nothing, [],  mapMaybe getWarns (tyCoVarsOfCtList ct))
   where getWarns var =
           case lookupFamInstEnv famInsts ptc_default [varType var] of
             [FamInstMatch {fim_instance=FamInst{..}, ..}] ->
               let predTy = mkPrimEqPredRole Nominal (mkTyVarTy var) fi_rhs
               in Just $ Log predTy (ctFlavour ct) (ctLoc ct)
             _ -> Nothing
solveWarnDefault _ _ _ ct = return $ Left ct


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
               report <- newReport ptc_report (Log new_rhs (ctFlavour ct) (ctLoc ct))
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
            case  (lookupFamInstEnv famInsts ptc_relate [k1, ty1, ty2])
               ++ (lookupFamInstEnv famInsts ptc_relate [k1, ty2, ty1]) of
               [] -> return $ Left ct
               (FamInstMatch {fim_instance=FamInst{..}, ..}:_) ->
                  do let new_rhs = substTyWith fi_tvs fim_tys fi_rhs
                         new_ev = (ctEvidence ct) {ctev_pred = new_rhs}
                     report <- newReport ptc_report (Log new_rhs (ctFlavour ct) (ctLoc ct))
                     return $ Right ( Just (mkProof "Relateable" Nominal ty1 ty2, ct)
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
                report <- newReport ptc_report (Log new_rhs (ctFlavour ct) (ctLoc ct))
                return $ Right ( Just (mkProof "Promoteable" Representational ty1 ty2, ct)
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
      Just r@(tyCon, [msg]) | getName tyCon == (getName ptc_report) ->
             Right (Just (mkProof "Reportable" Phantom (ctPred ct) msg, ct),
                   [], [Log msg (ctFlavour ct) (ctLoc ct)])
      _ -> Left ct

newReport :: TyCon -> Log -> TcPluginM Ct
newReport ptc_report (Log msg _ loc) =
    do ev <- newWanted loc (mkTyConApp ptc_report [msg])
       return $ setCtLoc CNonCanonical{cc_ev=ev} loc

-- Utils
mkProof :: String -> Role -> Type -> Type -> EvTerm
mkProof str role ty1 ty2 = evCoercion $ mkUnivCo (PluginProv str) role ty1 ty2

inspectSol :: [Either a (Maybe b, [c], [d])] -> ([a], ([b], [c], [d]))
inspectSol xs = (ls, (catMaybes sols, concat more, concat logs))
  where (ls, rs) = partitionEithers xs
        (sols, more, logs) = unzip3 rs
