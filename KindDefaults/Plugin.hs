-- Copyright (c) 2020 Matthías Páll Gissurarson
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecordWildCards #-}
module KindDefaults.Plugin (
      plugin,
      Defaultable, Collapsible, Promoteable, Ignoreable
      ) where

import GhcPlugins hiding (TcPlugin)
import TcRnTypes
import TcPluginM
import Constraint 
import ErrUtils (Severity(SevWarning))
import TcEvidence (EvTerm, evCoercion)

import Control.Monad (when, guard)
import Data.Maybe (mapMaybe, catMaybes, fromMaybe)
import Data.Either
import Data.IORef
import Data.List (nub, sort)
import Data.Function (on)

import FamInstEnv
import Finder (findPluginModule)
import LoadIface (loadPluginInterface)
import TcRnMonad (initIfaceTcRn)

import TysPrim (equalityTyCon)
import PrelNames (eqPrimTyConKey)
import Predicate (EqRel(NomEq), isEqPrimPred)

import Data.Kind (Constraint)

import GHC.TypeLits(TypeError(..), ErrorMessage(..))

thisModName :: ModuleName
thisModName = mkModuleName "KindDefaults.Plugin"

--------------------------------------------------------------------------------
-- Exported

plugin :: Plugin
plugin = defaultPlugin { tcPlugin = Just . kindDefaultPlugin
                       , pluginRecompile = purePlugin }


-- Defaultable means that if we have an ambiguous l1 of kind k, we can default
-- it to be the rhs, i.e. type family Defaultable Label = L would default all
-- ambiguous type variables of kind Label to L
type family Defaultable k :: (k,ErrorMessage)

-- Promoteable means that if we have a value (True :: Bool), we can promote it
-- to (k Bool)
type family Promoteable k :: a -> ErrorMessage

-- An ignoreable constraint means that we don't care if it isn't solved. Note!
-- This only works for empty classes!
type family Ignoreable (k :: Constraint) :: ErrorMessage

-- Collapsible means we are allowed to discharge (l1 :: k) ~ (l2 :: k)
type family Collapsible k :: ErrorMessage

--------------------------------------------------------------------------------

data Log = LogDefaultable Type CtLoc
         | LogIgnoreable Type CtLoc
         | LogCollapsible Type CtLoc
         | LogPromoteable Type CtLoc

logSrc :: Log -> CtLoc
logSrc (LogDefaultable _ l) = l
logSrc (LogIgnoreable _ l) = l
logSrc (LogCollapsible _ l) = l
logSrc (LogPromoteable _ l) = l

instance Ord Log where
  compare = compare `on` (ctLocSpan . logSrc)

instance Eq Log where
   LogIgnoreable t1 l1 == LogIgnoreable t2 l2 =
       ctLocSpan l1 == ctLocSpan l2 && t1 `eqType` t2
   LogCollapsible a1 l1 == LogCollapsible a2 l2 =
       ctLocSpan l1 == ctLocSpan l2 && a1 `eqType` a2
   LogPromoteable a1 l1 == LogPromoteable a2 l2 =
       ctLocSpan l1 == ctLocSpan l2 && a1 `eqType` a2
   LogDefaultable v1 l1 == LogDefaultable v2 l2 =
       ctLocSpan l1 == ctLocSpan l2 && v1 `eqType` v2
   _ == _ = False

instance Outputable Log where
   ppr (LogDefaultable ty _) = text "Defaulting:" <+> pprUserTypeErrorTy ty
   ppr (LogIgnoreable ty _)  = text "Ignoring:" <+> pprUserTypeErrorTy ty
   ppr (LogCollapsible ty _) = text "Collapsing:" <+> pprUserTypeErrorTy ty
   ppr (LogPromoteable ty _) = text "Promoting:" <+> pprUserTypeErrorTy ty

addWarning :: DynFlags -> Log -> IO()
addWarning dflags log = warn (ppr log)
  where
      warn = putLogMsg dflags NoReason SevWarning
                      (RealSrcSpan $ ctLocSpan $ logSrc log)
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
        ; mapM_ (pprDebug "Derived:") derived
        ; mapM_ (pprDebug "Wanted:") wanted
        ; instEnvs <- getFamInstEnvs
        ; pluginTyCons <- getPluginTyCons
        ; (extra, proofs) <- return ([], [])
        ; unsolved <- return wanted
        -- TODO: These are all almost identical, they could probably be 
        -- collapsed (pun intended) in a nice way.
        -- Ignoreables
        ; (unsolved, (solved, more, logs)) <-
            inspectSol <$> mapM (solveIgnoreable mode instEnvs pluginTyCons) unsolved
        ; mapM_ (pprDebug "Ignoring:") solved
        ; tcPluginIO $ modifyIORef warns (logs ++) 
        ; (extra, proofs) <- return (extra ++ more, proofs ++ solved)
        -- Defaultables
        ; (unsolved, (solved, more, logs)) <-
            inspectSol <$> mapM (solveDefaultable mode instEnvs pluginTyCons) unsolved
        ; mapM_ (pprDebug "Defaulting:") more
        ; tcPluginIO $ modifyIORef warns (logs ++) 
        ; (extra, proofs) <- return (extra ++ more, proofs ++ solved)
        -- Collapsibles
        ; (unsolved, (solved, more, logs)) <-
            inspectSol <$> mapM (solveCollapsible mode instEnvs pluginTyCons) unsolved
        ; mapM_ (pprDebug "Collapsing:") solved
        ; tcPluginIO $ modifyIORef warns (logs ++) 
        ; (extra, proofs) <- return (extra ++ more, proofs ++ solved)
        -- Promoteables
        ; (unsolved, (solved, more, logs)) <-
            inspectSol <$> mapM (solvePromoteable mode instEnvs pluginTyCons) unsolved
        ; mapM_ (pprDebug "Promoting:") solved
        ; tcPluginIO $ modifyIORef warns (logs ++) 
        ; (extra, proofs) <- return (extra ++ more, proofs ++ solved)

        ; return $ TcPluginOk proofs extra }
     stop warns =
        do { dflags <- unsafeTcPluginTcM getDynFlags
           ; when (mode == Defer) $
                tcPluginIO $ readIORef warns >>=
                    mapM_ (addWarning dflags) . sort . nub }

data PluginTyCons = PTC { defaultable :: TyCon
                        , collapsible  :: TyCon
                        , promoteable :: TyCon
                        , ignoreable   :: TyCon }

getPluginTyCons :: TcPluginM PluginTyCons
getPluginTyCons =
   do env <- getTopEnv
      fpmRes <- findImportedModule thisModName (Just $ mkFastString "kind-default-plugin")
      case fpmRes of
         Found _ mod  ->
             do defaultable <- getTyCon mod "Defaultable"
                collapsible <- getTyCon mod "Collapsible"
                promoteable <- getTyCon mod "Promoteable"
                ignoreable  <- getTyCon mod "Ignoreable"
                return $ PTC { defaultable = defaultable,
                               collapsible = collapsible,
                               promoteable = promoteable,
                               ignoreable  = ignoreable }
         _ -> pprPanic "Plugin module not found!" empty
  where getTyCon mod name = lookupOrig mod (mkTcOcc name) >>= tcLookupTyCon


type Solution = Either Ct (Maybe (EvTerm, Ct),-- The solution to the Ct
                           [Ct],-- Possible additional work
                           [Log])


solveDefaultable :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveDefaultable NoDefer _ _ ct = return $ Left ct
solveDefaultable Defer famInsts PTC{..} ct =
   do (cts, logs) <- unzip . catMaybes <$> mapM mkDefaultCt (tyCoVarsOfCtList ct)
      if null cts && null logs
      then return $ Left ct 
      else return $ Right (Nothing, cts, logs)
   where tyVars = tyCoVarsOfCtList ct
         mkDefaultCt var =
           case lookupFamInstEnv famInsts defaultable [varType var] of
             [FamInstMatch {fim_instance=FamInst{fi_rhs=def}}] ->
                case splitTyConApp_maybe def of
                   Just (_, [k1,k2,dTo,msg]) | k1 `eqType` (varType var) ->
                      do ref <- tcPluginIO $ newIORef Nothing
                         let kind = varType var
                             eqTo = dTo
                             eqNom = equalityTyCon Nominal
                             predTy = mkTyConApp eqNom [kind, kind, mkTyVarTy var, eqTo]
                             hole = CoercionHole {ch_co_var=var, ch_ref = ref}
                             ev = CtWanted {ctev_pred = predTy, ctev_nosh = WDeriv,
                                            ctev_dest = HoleDest hole,
                                            ctev_loc = ctLoc ct}
                         return $ Just (CTyEqCan {cc_ev = ev, cc_tyvar = var,
                                                  cc_rhs = eqTo, cc_eq_rel = NomEq},
                                         LogDefaultable (fromMaybe msg (userTypeError_maybe msg)) (ctLoc ct))
             _ -> return Nothing

solveIgnoreable :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveIgnoreable mode famInsts PTC{..} ct =
   case lookupFamInstEnv famInsts ignoreable [ctPred ct] of
      [] -> return $ Left ct
      [FamInstMatch {fim_instance=FamInst{fi_rhs=def}}] ->
          do nw <- return $ (ctEvidence ct) {ctev_pred = def}
             return $ Right (Just (evCoercion coercion, ct),
                              case mode of
                                Defer -> []
                                NoDefer -> [CNonCanonical {cc_ev=nw}],
                             [LogIgnoreable  (fromMaybe def $ userTypeError_maybe def) (ctLoc ct)])
   where (coercion, _) = normaliseType famInsts Phantom (ctPred ct)

solveCollapsible :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveCollapsible mode famInsts PTC{..} ct =
   case splitTyConApp_maybe (ctPred ct) of 
      Just (tyCon, [k1,k2,ty1,ty2]) | isEqPrimPred (ctPred ct)
                                      && k1 `eqType` k2 ->
            case lookupFamInstEnv famInsts collapsible [k1] of
               [] -> return $ Left ct
               [FamInstMatch {fim_instance=FamInst{fi_rhs=def}}] ->
                  do nw <- return $ (ctEvidence ct) {ctev_pred = def}
                     return $ Right (Just (evCoercion $ mkReflCo Phantom ty2, ct),
                                     case mode of
                                       Defer -> []
                                       NoDefer -> [CNonCanonical {cc_ev=nw}],
                                      [LogCollapsible (fromMaybe def $ userTypeError_maybe def) (ctLoc ct)])
      _ -> return $ Left ct

solvePromoteable :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solvePromoteable mode famInsts PTC{..} ct =
   case splitTyConApp_maybe (ctPred ct) of 
      Just r@(tyCon, args@[k1,k2,ty1,ty2]) | getUnique tyCon == eqPrimTyConKey
                                             && k1 `eqType` k2 ->
        case lookupFamInstEnv famInsts promoteable [ty1, ty2] of
           [] ->return $ Left ct
           [FamInstMatch {fim_instance=FamInst{fi_rhs=def}}] ->
             do let pty = case mode of
                            Defer -> mkTyConApp eqRep args
                            NoDefer -> def
                nw <- return $ (ctEvidence ct) {ctev_pred = pty}
                return $ Right (Just (evCoercion $ mkReflCo Representational ty2, ct),
                               [CNonCanonical {cc_ev=nw}],
                               [LogPromoteable (fromMaybe def $ userTypeError_maybe def) (ctLoc ct)])
      _ -> return $ Left ct
  where eqRep = equalityTyCon Representational

inspectSol :: [Either a (Maybe b, [c], [d])] -> ([a], ([b], [c], [d]))
inspectSol xs = (ls, (catMaybes sols, concat more, concat logs))
  where (ls, rs) = partitionEithers xs
        (sols, more, logs) = unzip3 rs