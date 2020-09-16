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
import Data.List (intersperse, or, partition)
import Data.Function (on)
import Data.Kind (Constraint)
import Data.Data (Data, toConstr)
import Prelude hiding ((<>))
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Proxy
import Data.Dynamic
import Type.Reflection (someTypeRep)

import GHC.TypeLits(TypeError(..), ErrorMessage(..))

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import System.IO.Unsafe (unsafePerformIO)

import Bag

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

import TcType
import CoAxiom
import Unify


--- PostProcess
import HsBinds
import HsExtension
import HsExpr
import TcEvTerm (evCallStack)
-------

-- Holefits
import RdrName (globalRdrEnvElts)
import TcRnMonad (getGlobalRdrEnv, captureConstraints, pushLevelAndCaptureConstraints)
import TcHoleErrors
import PrelInfo (knownKeyNames)
import Data.Graph (graphFromEdges, topSort)
import Control.Monad (filterM)
import DsBinds (dsHsWrapper)
import DsMonad (initDsTc)

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
  compare = compare `on` logSrc

instance Eq Log where
   a@Log{} == b@Log{} =
       ((==) `on` logSrc) a b && (eqType `on` log_pred_ty) a b
   a@LogDefault{} == b@LogDefault{} =
       ((==) `on` logSrc) a b && (eqType `on` log_pred_ty) a b
                              && ((==) `on` log_var) a b
   a@LogMarshal{} == b@LogMarshal{} =
       ((==) `on` logSrc) a b && (eqType `on` log_pred_ty) a b
   a@LogSDoc{} == b@LogSDoc{} =
       ((==) `on` logSrc) a b && (eqType `on` log_pred_ty) a b

   Log{} == _ = False
   LogDefault{} == _ = False
   LogMarshal{} == _ = False
   LogSDoc{} == _ = False

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
                   , f_marshal_dynamics :: Bool } deriving (Show)

getFlags :: [CommandLineOption] -> Flags
getFlags opts = Flags { f_debug                 = "debug"            `elem` opts
                      , f_quiet                 = "quiet"            `elem` opts
                      , f_keep_errors           = "keep-errors"      `elem` opts
                      , f_marshal_dynamics      = "marshal-dynamics" `elem` opts }

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
                   , (solveHole, "Hole")
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
                   , dc_cast_dyn :: Id
                   , dc_has_call_stack :: TyCon }

getPluginTyCons :: TcPluginM PluginTyCons
getPluginTyCons =
   do fpmRes <- findImportedModule (mkModuleName "WRIT.Configure") Nothing
      dc_dynamic <- getTyCon dYNAMIC "Dynamic"
      dc_typeable <- getClass tYPEABLE_INTERNAL "Typeable"
      dc_to_dyn <- getId dYNAMIC "toDyn"
      dc_has_call_stack <- getTyCon gHC_STACK_TYPES "HasCallStack"

      case fpmRes of
         Found _ mod  ->
             do ptc_default <- getTyCon mod "Default"
                ptc_discharge  <- getTyCon mod "Discharge"
                ptc_promote <- getTyCon mod "Promote"
                ptc_ignore  <- getTyCon mod "Ignore"
                ptc_msg     <- getPromDataCon mod "Msg"
                ptc_only_if <- getPromDataCon mod "OnlyIf"
                dc_cast_dyn <- getId mod "castDyn"
                let ptc_dc = DC {..}
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


-- | Solves Γ |- (a :: k) ~ (b :: k) if Γ |- Discharge a b ~ Msg m.
-- Requires flags for marshal-dynamics
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
          dynamic = mkTyConApp dc_dynamic []
          isDyn ty = ty `tcEqType` dynamic
      missingPromote <- (&&) kIsType . not <$> hasInst promote
      if not hasDischarge || missingPromote
      then if kIsType && (isDyn ty1 || isDyn ty2)
           then marshalDynamic k1 ty1 ty2 ptc ct
           else wontSolve ct
      else do (msg_check, msg_var) <- checkMsg ptc ct discharge
              let log = Set.singleton (Log msg_var (ctLoc ct))
                  proof = mkProof "grit-discharge" ty1 ty2
              couldSolve (Just (proof, ct)) [msg_check] log
    _ -> wontSolve ct

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

-- Dynamic extension:

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
coreDyn clo tds = return $ (CoreDoPluginPass "WRIT" $ bindsOnlyPass addDyn):tds
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

-- Typed-Holes
solveHole :: SolveFun
solveHole ptc@PTC{..} ct@CHoleCan{cc_ev=CtWanted{ctev_dest=EvVarDest evVar},
                                  cc_hole=hole@(ExprHole (TrueExprHole occ))} =
  do let ty = ctPred ct
     fits <- do
#if __GLASGOW_HASKELL__ >= 810
      hfPlugs <- tcg_hf_plugins <$> getGblEnv
      let ty_h = TyH emptyBag [] (Just ct)
          (candidatePlugins, fitPlugins) =
             unzip $ map (\p-> ((candPlugin p) hole, (fitPlugin p) ct))
#else
      let (candidatePlugins, fitPlugins) = ([],[])
#endif
      unsafeTcPluginTcM $ getCandsInScope ct
                        >>= flip (foldM (flip ($))) candidatePlugins
                        >>= fmap snd . tcFilterHoleFits Nothing [] [] (ty, [])
                        >>= sortByGraph
                        >>= flip (foldM (flip ($))) fitPlugins
     -- We should pick a good "fit" here, taking the first after sorting by
     -- subsumption is something, but picking a good fit is a whole research
     -- field.
     case fits of
       (fit:_) -> do
         let log = Set.singleton $ LogSDoc ty (ctLoc ct) $ text "replacing"
                     <+> quotes (ppr (holeOcc hole) <+> dcolon <+> ppr (ctPred ct))
                     <+> text "with" <+> quotes (ppr (hfId fit))
         (core, needed) <- unsafeTcPluginTcM $ candToCore ct fit
         couldSolve (Just (EvExpr core , ct)) needed log
       _ -> wontSolve ct
solveHole _ ct = wontSolve ct

candToCore :: Ct -> HoleFit -> TcM (CoreExpr, [Ct])
candToCore ct fit@HoleFit{..}  = do
    --check_cts <- mapM (fmap exportWanted . mkWanted (ctLoc ct)) checks
    -- We know it's going to be true, since it came from tcFilterHoleFits. We
    -- also don't have to worry about unification, since we're explicitly using
    -- THIS fit.
    ((True, wrp)) <- tcCheckHoleFit emptyBag [] (ctPred ct) hfType
    term <- ($ Var hfId) <$> (initDsTc $ dsHsWrapper wrp)
    let evVars = nonDetEltsUniqSet $ evVarsOfTerm (EvExpr term)
    return (term, map evToCt evVars)
  where evToCt :: EvVar -> Ct
        evToCt var = CNonCanonical (CtWanted{..})
          where ctev_dest = EvVarDest (setIdExported var)
                ctev_loc = ctLoc ct
                ctev_pred = varType var
                ctev_nosh = WDeriv

-- From TcHoleErrors (it's not exported)
getCandsInScope :: Ct -> TcM [HoleFitCandidate]
getCandsInScope ct = do
  rdr_env <- getGlobalRdrEnv
  lcl_binds <- getLocalBindings ct
  let (lcl, gbl) = partition gre_lcl (globalRdrEnvElts rdr_env)
      locals = removeBindingShadowing $ map IdHFCand lcl_binds
                                        ++ map GreHFCand lcl
      builtIns = filter isBuiltInSyntax knownKeyNames
      globals = map GreHFCand gbl
      syntax = map NameHFCand builtIns
  return $ locals ++ syntax ++ globals
  where getLocalBindings :: Ct -> TcM [Id]
        getLocalBindings ct =
          go [] (removeBindingShadowing $ tcl_bndrs lcl_env)
          where loc     = ctEvLoc (ctEvidence ct)
                lcl_env = ctLocEnv loc
                go :: [Id] -> [TcBinder] -> TcM [Id]
                go sofar [] = return (reverse sofar)
                go sofar (tc_bndr : tc_bndrs) =
                    case tc_bndr of
                      TcIdBndr id _ -> keep_it id
                      _ -> discard_it
                  where discard_it = go sofar tc_bndrs
                        keep_it id = go (id:sofar) tc_bndrs

-- Also from TcHoleErrors
sortByGraph :: [HoleFit] -> TcM [HoleFit]
sortByGraph fits = go [] fits
  where tcSubsumesWCloning :: TcType -> TcType -> TcM Bool
        tcSubsumesWCloning ht ty = withoutUnification fvs (tcSubsumes ht ty)
          where fvs = tyCoFVsOfTypes [ht,ty]
        hfIsLcl :: HoleFit -> Bool
        hfIsLcl hf = case hfCand hf of
                      IdHFCand _    -> True
                      NameHFCand _  -> False
                      GreHFCand gre -> gre_lcl gre
        go :: [(HoleFit, [HoleFit])] -> [HoleFit] -> TcM [HoleFit]
        go sofar [] = return $ uncurry (++) $ partition hfIsLcl topSorted
          where toV (hf, adjs) = (hf, hfId hf, map hfId adjs)
                (graph, fromV, _) = graphFromEdges $ map toV sofar
                topSorted :: [HoleFit]
                topSorted = map ((\(h,_,_) -> h) . fromV) $ topSort graph
        go sofar (hf:hfs) =
          do { adjs <-
                 filterM (tcSubsumesWCloning (hfType hf) . hfType) fits
             ; go ((hf, adjs):sofar) hfs }