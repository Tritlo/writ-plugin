-- Copyright (c) 2020 Matthías Páll Gissurarson
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE QuantifiedConstraints #-}
module KindDefaults.Plugin (
      plugin,
      Default, Promote, Ignore, Relate,
      ) where

import GhcPlugins hiding (TcPlugin)
import TcRnTypes
import TcPluginM
import Constraint 
import ErrUtils (Severity(SevWarning))
import TcEvidence (EvTerm, evCoercion)

import Control.Monad (when, guard, foldM)
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
import Data.Data (Data, toConstr)

import GHC.TypeLits(TypeError(..), ErrorMessage(..))

thisModName :: ModuleName
thisModName = mkModuleName "KindDefaults.Plugin"

--------------------------------------------------------------------------------
-- Exported

plugin :: Plugin
plugin = defaultPlugin { tcPlugin = Just . kindDefaultPlugin
                       , pluginRecompile = purePlugin }


-- Default means that if we have an ambiguous l1 of kind k, we can default it to
-- be the rhs, i.e. type family Default Label = L would default all
-- ambiguous type variables of kind Label to L
type family Default k :: k

-- Promote means that if we have a value (True :: Bool), we can promote it to (k Bool)
-- Note that Promote a k requires Coercible a k, otherwise a Coercible error  will be produced.
type family Promote (a :: *) (k :: *) :: ErrorMessage

-- An ignore constraint means that we don't care if it isn't solved. 
-- Note! This only works for empty classes!
type family Ignore (k :: Constraint) :: ErrorMessage

-- Relate means that we are allowed to discharge (a :: k) ~ (b :: k) and (b :: k) ~ (a :: k).
type family Relate k (a :: k) (b :: k):: ErrorMessage
--------------------------------------------------------------------------------

data Log = Log Type CtLoc

logSrc :: Log -> RealSrcSpan
logSrc (Log _ l) = ctLocSpan l

logTy :: Log -> Type
logTy (Log t _) = t

-- Log prec determines in which order the warnings show up if  two show up in
-- the same location. We want Default to show up first, since it's often the
-- case that the others are a result of having defaulted a type variable.

instance Ord Log where
  compare = compare `on` logSrc

instance Eq Log where
   logA == logB =
       (((==) `on` logSrc) logA logB) && ((eqType `on` logTy) logA logB)

instance Outputable Log where
   -- We do some extra work to pretty print the Defaulting messages
   ppr (Log ty _) =
        case userTypeError_maybe ty of
           Just msg -> pprUserTypeErrorTy msg
           _ ->  case splitTyConApp_maybe ty of
                   Just (tc, [k1,k2,ty1,ty2]) | isEqPrimPred ty
                                               && isTyVarTy ty1 ->
                        text "Defaulting"
                        -- We want to print a instead of a0
                        <+> ppr (occName $ getTyVar "isTyVarTy lied!" ty1)
                        <+> dcolon <+> ppr k1
                        <+> text "to" <+>
                              -- We want to print L instead of 'L if possible
                              case (do (tc, []) <- splitTyConApp_maybe ty2
                                       dc <- isPromotedDataCon_maybe tc
                                       return dc) of
                                 Just dc -> ppr dc
                                 _ -> ppr ty2
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
        ; (unsolved, (solved, more, logs)) <-
             foldM solveWFun (wanted, ([],[],[])) [ (solveReport, "Reporting")
                                                  , (solveDefault, "Defaulting")
                                                  , (solveRelate,  "Relating")
                                                  , (solveIgnore,  "Ignoring")
                                                  , (solvePromote, "Promoting") ]
        ; tcPluginIO $ modifyIORef warns (logs ++) 
        ; return $ TcPluginOk solved more }
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
   do env <- getTopEnv
      fpmRes <- findImportedModule thisModName (Just $ mkFastString "kind-default-plugin")
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
         _ -> pprPanic "Plugin module not found!" empty
  where getTyCon mod name = lookupOrig mod (mkTcOcc name) >>= tcLookupTyCon


type Solution = Either Ct (Maybe (EvTerm, Ct), -- The solution to the Ct
                           [Ct],               -- Possible additional work
                           [Log])              -- What we did



-- Defaults any ambiguous type variables of kind k to l if Default k = l
solveDefault :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveDefault _ famInsts PTC{..} ct =
   do (cts, logs) <- unzip . catMaybes <$> mapM mkDefaultCt (tyCoVarsOfCtList ct)
      if null cts && null logs
      then return $ Left ct 
      else return $ Right (Nothing, cts, logs)
   where tyVars = tyCoVarsOfCtList ct
         mkDefaultCt var =
           case lookupFamInstEnv famInsts ptc_default [varType var] of
             [FamInstMatch {fim_instance=FamInst{..}, ..}] ->
               do ref <- tcPluginIO $ newIORef Nothing
                  let kind = varType var
                      -- Here we shortcut and output var ~ def, but we could also
                      -- use the type family directly by writing
                      --      rhs = mkTyConApp ptc_default [kind]
                      -- which would result in var ~ Default kind
                      rhs = fi_rhs
                      eqNom = equalityTyCon Nominal
                      predTy = mkTyConApp eqNom [kind, kind, mkTyVarTy var, rhs]
                      hole = CoercionHole {ch_co_var=var, ch_ref = ref}
                      ev = CtWanted {ctev_pred = predTy , ctev_nosh = WDeriv,
                                     ctev_dest = HoleDest hole,
                                     ctev_loc = ctLoc ct}
                  return $ Just (CTyEqCan {cc_ev = ev, cc_tyvar = var,
                                          cc_rhs = rhs, cc_eq_rel = NomEq},
                                 Log predTy (ctLoc ct))
             _ -> return Nothing


-- Solves con :: Constraint if Ignore con
solveIgnore :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveIgnore mode famInsts PTC{..} ct =
   case lookupFamInstEnv famInsts ptc_ignore [ctPred ct] of
      [] -> return $ Left ct
      [FamInstMatch {fim_instance=FamInst{..}, ..}] ->
            do let new_rhs = substTyWith fi_tvs fim_tys fi_rhs
                   new_ev = (ctEvidence ct) {ctev_pred = new_rhs}
               report <- newReport ptc_report (Log new_rhs (ctLoc ct))
               return $ Right (Just (evCoercion coercion, ct),
                        case mode of
                           Defer -> [report]
                           NoDefer -> [CNonCanonical {cc_ev=new_ev}],
                        [])
   where (coercion, _) = normaliseType famInsts Phantom (ctPred ct)


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
                     report <- newReport ptc_report (Log new_rhs (ctLoc ct))
                     return $ Right ( Just (evCoercion $ mkReflCo Phantom ty2, ct)
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
                return $ Right ( Just (evCoercion $ mkReflCo Representational ty2, ct)
                               , case mode of
                                   Defer -> [report, CNonCanonical {cc_ev=new_ev}]
                                   NoDefer -> [CNonCanonical {cc_ev=new_ev}]
                               , [])
      _ -> return $ Left ct
  where eqRep = equalityTyCon Representational

type family Report (err :: ErrorMessage)  :: Constraint
-- Solve Report is our way of computing whatever type familes that might be in
-- a given type error before emitting it as a warning.
solveReport :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveReport _ _ PTC{..} ct = return $
   case splitTyConApp_maybe (ctPred ct) of
      Just r@(tyCon, [msg]) | getName tyCon == (getName ptc_report) ->
             Right (Just (evCoercion $ mkReflCo Phantom msg, ct),
                   [], [Log msg (ctLoc ct)])
      _ -> Left ct

newReport :: TyCon -> Log -> TcPluginM Ct
newReport ptc_report (Log msg loc) = 
    do ev <- newWanted loc (mkTyConApp ptc_report [msg])
       return $ setCtLoc CNonCanonical{cc_ev=ev} loc

-- Utils

inspectSol :: [Either a (Maybe b, [c], [d])] -> ([a], ([b], [c], [d]))
inspectSol xs = (ls, (catMaybes sols, concat more, concat logs))
  where (ls, rs) = partitionEithers xs
        (sols, more, logs) = unzip3 rs