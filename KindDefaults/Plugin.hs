-- Copyright (c) 2020 Matthías Páll Gissurarson
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveDataTypeable #-}
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


-- Defaultable means that if we have an ambiguous l1 of kind k, we can default
-- it to be the rhs, i.e. type family Defaultable Label = L would default all
-- ambiguous type variables of kind Label to L
type family Defaultable k :: k

-- Promoteable means that if we have a value (True :: Bool), we can promote it
-- to (k Bool)
type family Promoteable k :: a -> ErrorMessage

-- An ignoreable constraint means that we don't care if it isn't solved. Note!
-- This only works for empty classes!
type family Ignoreable (k :: Constraint) :: ErrorMessage

-- Collapsible means we are allowed to discharge (l1 :: k) ~ (l2 :: k)
type family Collapsible k :: ErrorMessage

--------------------------------------------------------------------------------

data Log = LogDefaultable Type RealSrcSpan
         | LogCollapsible Type RealSrcSpan
         | LogPromoteable Type RealSrcSpan
         | LogIgnoreable  Type RealSrcSpan deriving (Data)

logSrc :: Log -> RealSrcSpan
logSrc (LogDefaultable _ l) = l
logSrc (LogCollapsible _ l) = l
logSrc (LogPromoteable _ l) = l
logSrc (LogIgnoreable  _ l) = l

logTy :: Log -> Type
logTy (LogDefaultable t _) = t
logTy (LogCollapsible t _) = t
logTy (LogPromoteable t _) = t
logTy (LogIgnoreable  t _) = t

-- Log prec determines in which order the warnings show up if  two show up in
-- the same location. We want Defaultable to show up first, since it's often the
-- case that the others are a result of having defaulted a type variable.
logPrec :: Log -> Int
logPrec (LogDefaultable t _) = 1
logPrec (LogCollapsible t _) = 2
logPrec (LogPromoteable t _) = 3
logPrec (LogIgnoreable  t _) = 4

instance Ord Log where
  compare a b = case (compare `on` logSrc) a b of
                    EQ -> (compare `on` logPrec) a b
                    r -> r

instance Eq Log where
   logA == logB = (((==) `on` toConstr) logA logB)
                  && (((==) `on` logSrc) logA logB)
                  && ((eqType `on` logTy) logA logB)

instance Outputable Log where
   ppr (LogDefaultable ty _) = text "Defaulting:" <+> pprUserTypeErrorTy ty
   ppr (LogCollapsible ty _) = text "Collapsing:" <+> pprUserTypeErrorTy ty
   ppr (LogPromoteable ty _) = text "Promoting:"  <+> pprUserTypeErrorTy ty
   ppr (LogIgnoreable  ty _) = text "Ignoring:"   <+> pprUserTypeErrorTy ty

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
             foldM solveWFun (wanted, ([],[],[])) [ (solveIgnoreable, "Ignoring")
                                                  , (solveDefaultable, "Defaulting")
                                                  , (solveCollapsible, "Collapsing")
                                                  , (solvePromoteable, "Promoting") ]
        ; tcPluginIO $ modifyIORef warns (logs ++) 
        ; return $ TcPluginOk solved more }
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


type Solution = Either Ct (Maybe (EvTerm, Ct), -- The solution to the Ct
                           [Ct],               -- Possible additional work
                           [Log])              -- What we did


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
               do ref <- tcPluginIO $ newIORef Nothing
                  let kind = varType var
                      -- Here we shortcut and output var ~ def, but we could also
                      -- use the type family directly by writing
                      --      rhs = mkTyConApp defaultable [kind]
                      -- which would result in var ~ Defaultable kind
                      rhs = def
                      eqNom = equalityTyCon Nominal
                      predTy = mkTyConApp eqNom [kind, kind, mkTyVarTy var, rhs]
                      hole = CoercionHole {ch_co_var=var, ch_ref = ref}
                      ev = CtWanted {ctev_pred = predTy , ctev_nosh = WDeriv,
                                     ctev_dest = HoleDest hole,
                                     ctev_loc = ctLoc ct}
                  return $ Just (CTyEqCan {cc_ev = ev, cc_tyvar = var,
                                          cc_rhs = rhs, cc_eq_rel = NomEq},
                                 LogDefaultable predTy (ctLocSpan $ ctLoc ct))
             _ -> return Nothing

solveIgnoreable :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveIgnoreable mode famInsts PTC{..} ct =
   case lookupFamInstEnv famInsts ignoreable [ctPred ct] of
      [] -> return $ Left ct
      [FamInstMatch {fim_instance=FamInst{fi_rhs=def}}] ->
          do let new_ev = (ctEvidence ct) {ctev_pred = def}
             return $ Right (Just (evCoercion coercion, ct),
                              case mode of
                                Defer -> []
                                NoDefer -> [CNonCanonical {cc_ev=new_ev}],
                             [LogIgnoreable  (unwrapIfMsg def) (ctLocSpan $ ctLoc ct)])
   where (coercion, _) = normaliseType famInsts Phantom (ctPred ct)

solveCollapsible :: Mode -> FamInstEnvs -> PluginTyCons -> Ct -> TcPluginM Solution
solveCollapsible mode famInsts PTC{..} ct =
   case splitTyConApp_maybe (ctPred ct) of 
      Just (tyCon, [k1,k2,ty1,ty2]) | isEqPrimPred (ctPred ct)
                                      && k1 `eqType` k2 ->
            case lookupFamInstEnv famInsts collapsible [k1] of
               [] -> return $ Left ct
               [FamInstMatch {fim_instance=FamInst{fi_rhs=def}}] ->
                  do let new_ev = (ctEvidence ct) {ctev_pred = def}
                     return $ Right (Just (evCoercion $ mkReflCo Phantom ty2, ct),
                                     case mode of
                                       Defer -> []
                                       NoDefer -> [CNonCanonical {cc_ev=new_ev}],
                                      [LogCollapsible (unwrapIfMsg def) (ctLocSpan $ ctLoc ct)])
      _ -> return $ Left ct

-- Solve promoteable turns a ~ B c into Coercible a (B c)
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
                    nw = (ctEvidence ct) {ctev_pred = pty}
                return $ Right (Just (evCoercion $ mkReflCo Representational ty2, ct),
                               [CNonCanonical {cc_ev=nw}],
                               [LogPromoteable (unwrapIfMsg def) (ctLocSpan $ ctLoc ct)])
      _ -> return $ Left ct
  where eqRep = equalityTyCon Representational

-- Utils

unwrapIfMsg :: Type -> Type
unwrapIfMsg def = fromMaybe def $ userTypeError_maybe def

inspectSol :: [Either a (Maybe b, [c], [d])] -> ([a], ([b], [c], [d]))
inspectSol xs = (ls, (catMaybes sols, concat more, concat logs))
  where (ls, rs) = partitionEithers xs
        (sols, more, logs) = unzip3 rs