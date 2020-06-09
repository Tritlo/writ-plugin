-- Copyright (c) 2020 Matthias Pall Gissurarson
{-# LANGUAGE DataKinds #-}
module KindDefaults.Plugin  (plugin) where

import GhcPlugins hiding (TcPlugin)
import TcRnTypes
import TcPluginM
import Control.Monad (when, join)
import Constraint
import Data.Maybe (fromJust, isJust, mapMaybe)
import Data.IORef
import Data.List (nub, sort)
import Data.Function (on)
import PrelNames
import TcEvidence (EvTerm, evCoercion)
import ErrUtils
import Data.Data (Data)

import FamInst 
import FamInstEnv
import Finder 

import TysPrim (eqPrimTyCon)
import Predicate


import GHC.Hs


-- We have to add an import of GHC.TypeLits() to the module, otherwise we
-- can get funny messages about interface files being missing
addTypeLitImport :: HsParsedModule -> HsParsedModule
addTypeLitImport pm@HsParsedModule{hpm_module=L l m@HsModule{hsmodImports = imps}}
   = pm{hpm_module = L l m{hsmodImports = imp:imps}}
  where imp = noLoc (simpleImportDecl (moduleName gHC_TYPELITS)) {ideclHiding = Just (False, noLoc [])}


plugin :: Plugin
plugin = defaultPlugin { tcPlugin = Just . kindDefaultPlugin
                       , parsedResultAction = \_ _ -> return . addTypeLitImport
                       , pluginRecompile = purePlugin }


data Log = Defaulting TyCoVar Kind Type SrcSpan

logSrc :: Log -> SrcSpan
logSrc (Defaulting _ _ _ l) = l

instance Ord Log where
  compare = compare `on` logSrc

instance Eq Log where
   (==) = (==) `on` logSrc

addWarning :: DynFlags -> Log -> IO()
addWarning dflags log = warn (logMsg log)
  where
    warn =
      putLogMsg dflags NoReason SevWarning (logSrc log) (defaultErrStyle dflags)

logDefaulting :: DynFlags -> (TyCoVar, Kind, Type, CtLoc) -> Log
logDefaulting _ (var, kind, ty, loc) = Defaulting var kind ty (RealSrcSpan $ ctLocSpan loc)

logMsg :: Log -> SDoc
logMsg (Defaulting var kind ty _) = text "Defaulting" <+> ppr (occName var) <+>
                                    dcolon <+> ppr kind <+>
                                    text "to" <+> ppr ty

kindDefaultPlugin :: [CommandLineOption] -> TcPlugin
kindDefaultPlugin opts = TcPlugin initialize solve stop
  where
     debug = "debug" `elem` opts
     initialize = tcPluginIO $ newIORef []
     solve warns given derived wanted = do {
        ; dflags <- unsafeTcPluginTcM getDynFlags
        ; let pprDebug str a =
                when debug $
                  tcPluginIO $ putStrLn (str ++ " " ++ showSDoc dflags (ppr a))
        ; pprDebug "Solving" empty
        ; mapM_ (pprDebug "Given:") given
        ; mapM_ (pprDebug "Derived:") derived
        ; mapM_ (pprDebug "Wanted:") wanted
        ; instEnvs <- unsafeTcPluginTcM tcGetFamInstEnvs
        ; defaultToTyCon <- getDefaultTyCon
        ; let tvs = map (getTyVarDefaults instEnvs defaultToTyCon) wanted
        ; tcPluginIO $ modifyIORef warns (concatMap ( map (logDefaulting dflags)) tvs ++)
        ; mapM_ (pprDebug "TyVars:" . (map (\(a,b,c,_) -> (a,b,c)))) tvs
        ; let defs =  map (map (defaultEqConstraint defaultToTyCon)) tvs
        ; mapM_ (pprDebug "Defs:" ) defs
        ; defCts <- concat <$> mapM (mapM (defaultingCt defaultToTyCon)) tvs
        ; mapM_ (pprDebug "Defs:" ) defCts
        ; return $ TcPluginOk [] defCts }
     stop warns =
        do { dflags <- unsafeTcPluginTcM getDynFlags
           ; tcPluginIO $ readIORef warns >>=
                          mapM_ (addWarning dflags) . sort . nub }

defaultEqConstraint :: TyCon -> (TyCoVar, Kind, Type, CtLoc) -> Type
defaultEqConstraint defaultTyCon (var, kind, def, _) = 
      mkTyConApp eqPrimTyCon [kind, kind, mkTyVarTy var, eqTo]
 where --eqTo = var -- if we want direct
       eqTo = mkTyConApp defaultTyCon [kind]

defaultingCt :: TyCon -> (TyCoVar, Kind, Type, CtLoc) -> TcPluginM Ct
defaultingCt defaultTyCon (var, kind, def, loc) = 
   do ev <- getEv
      return $ CTyEqCan {cc_ev = ev, cc_tyvar = var,
                         cc_rhs = eqTo, cc_eq_rel=eqRel }
 where --eqTo = var -- if we want direct
       eqTo = mkTyConApp defaultTyCon [kind]
       predTy = mkTyConApp eqPrimTyCon [kind, kind, mkTyVarTy var, eqTo]
       eqRel = NomEq
       getEv = do ref <- tcPluginIO $ newIORef Nothing
                  let hole = CoercionHole {ch_co_var = var, ch_ref=ref} 
                  return $ CtWanted {ctev_pred = predTy, 
                                     ctev_nosh = WDeriv,
                                     ctev_dest = HoleDest hole,
                                     ctev_loc = loc}

getDefaultTyCon :: TcPluginM TyCon
getDefaultTyCon =
   do env <- getTopEnv
      fpmRes <- tcPluginIO $ findPluginModule env (mkModuleName "KindDefaults") 
      case fpmRes of
         Found _ mod  ->
            do name <- lookupOrig mod (mkTcOcc "DefaultTo")
               tcLookupTyCon name
         _ -> pprPanic "DefaultTo not found!" empty

getTyVarDefaults :: FamInstEnvs -> TyCon -> Ct -> [(TyCoVar, Kind, Type, CtLoc)]
getTyVarDefaults famInsts defaultToTyCon ct = mapMaybe getDefault tvs
  where tvs = tyCoVarsOfCtList ct 
        lookup kind = lookupFamInstEnv famInsts defaultToTyCon [kind]
        getDefault ty =
           case lookup  (varType ty) of
              [FamInstMatch {fim_instance=FamInst{fi_rhs=def}}] ->
                 Just (ty, varType ty, def, ctLoc ct)
              _ -> Nothing

isPrimEqTyCon :: TyCon -> Bool
isPrimEqTyCon tyCon = getUnique tyCon == eqPrimTyConKey

isTYPE :: Type -> Bool
isTYPE ty = case splitTyConApp_maybe ty of
            Just (t, _) ->  getUnique t == tYPETyConKey
            _ -> False