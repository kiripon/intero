{-# LANGUAGE CPP                 #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Get information on modules, identifiers, etc.

module GhciInfo (collectInfo,getModInfo,showppr) where

import           ConLike
import           Control.Exception
import           Control.Monad
import qualified CoreUtils
import           Data.Data
import qualified Data.Generics
import           Data.List
import           Data.Map.Strict   (Map)
import qualified Data.Map.Strict   as M
import           Data.Maybe
import           Data.Time
import           DataCon
import           Desugar
import           DynFlags
import           GHC
import           GhciTypes
import           GhcMonad
import           HscTypes
import           Intero.Compat
import           Outputable
import           Prelude           hiding (mod)
import           System.Directory
import           TcHsSyn
import           Var

-- | Collect type info data for the loaded modules.
collectInfo :: (GhcMonad m)
            => Map ModuleName ModInfo -> [ModuleName] -> m (Map ModuleName ModInfo)
collectInfo ms loaded =
  do df <- getSessionDynFlags
     -- Generate for all modules in interpreted mode.
     invalidated <-
       liftIO (if hscTarget df == HscInterpreted
                  then return loaded
                  else filterM cacheInvalid loaded)
     if null invalidated
        then return ms
        else do liftIO (putStrLn ("Collecting type info for " ++
                                  show (length invalidated) ++
                                  " module(s) ... "))
                foldM (\m name ->
                         gcatch (do info <- getModInfo name
                                    return (M.insert name info m))
                                (\(e :: SomeException) ->
                                   do liftIO (putStrLn ("Error while getting type info from " ++
                                                        showppr df name ++
                                                        ": " ++ show e))
                                      return m))
                      ms
                      invalidated
  where cacheInvalid name =
          case M.lookup name ms of
            Nothing -> return True
            Just mi ->
              do let fp =
                       ml_hi_file (ms_location (modinfoSummary mi))
                     last' = modinfoLastUpdate mi
                 exists <- doesFileExist fp
                 if exists
                    then do mod <- getModificationTime fp
                            return (mod > last')
                    else return True

-- | Get info about the module: summary, types, etc.
getModInfo :: (GhcMonad m) => ModuleName -> m ModInfo
getModInfo name =
  do m <- getModSummary name
     p <- parseModule m
     let location = getModuleLocation (parsedSource p)
     typechecked <- typecheckModuleSilent p
     let Just (_, imports, _, _) = renamedSource typechecked
     allTypes <- processAllTypeCheckedModule typechecked
     let i = tm_checked_module_info typechecked
     now <- liftIO getCurrentTime
     return (ModInfo m allTypes i now imports location)

-- | Type-check the module without logging messages.
typecheckModuleSilent :: GhcMonad m => ParsedModule -> m TypecheckedModule
typecheckModuleSilent parsed = do
  typecheckModule
    parsed
    { GHC.pm_mod_summary =
        (GHC.pm_mod_summary parsed)
        { HscTypes.ms_hspp_opts =
            (HscTypes.ms_hspp_opts (GHC.pm_mod_summary parsed))
            {log_action = nullLogAction}
        }
    }
  where
    nullLogAction _df _reason _sev _span _style _msgdoc = return ()

getModuleLocation :: ParsedSource -> SrcSpan
getModuleLocation pSource = case hsmodName (unLoc pSource) of
  Just located -> getLoc located
  Nothing      -> noSrcSpan

-- | Get ALL source spans in the module.
processAllTypeCheckedModule :: GhcMonad m
                            => TypecheckedModule -> m [SpanInfo]
processAllTypeCheckedModule tcm =
  do let tcs = tm_typechecked_source tcm
         bs = listifyAllSpans tcs :: [LHsBind StageReaderId]
         es = listifyAllSpans tcs :: [LHsExpr StageReaderId]
         ps = listifyAllSpans tcs :: [LPat StageReaderId]
     bts <- mapM (getTypeLHsBind tcm) bs
     ets <- mapM (getTypeLHsExpr tcm) es
     pts <- mapM (getTypeLPat tcm) ps
     return (mapMaybe toSpanInfo (sortBy cmp (concat bts ++ catMaybes (concat [ets,pts]))))
  where cmp (_,a,_) (_,b,_)
          | a `isSubspanOf` b = LT
          | b `isSubspanOf` a = GT
          | otherwise = EQ

getTypeLHsBind :: (GhcMonad m)
               => TypecheckedModule
               -> LHsBind StageReaderId
               -> m [(Maybe Id,SrcSpan,Type)]
getTypeLHsBind _ (L _spn FunBind{fun_id = pid,fun_matches = MG{}}) =
  return (return (Just (unLoc pid),getLoc pid,varType (unLoc pid)))
getTypeLHsBind _ _ = return []
-- getTypeLHsBind _ x =
--   do df <- getSessionDynFlags
--      error ("getTypeLHsBind: unhandled case: " ++
--             showppr df x)

getTypeLHsExpr :: (GhcMonad m)
               => TypecheckedModule
               -> LHsExpr StageReaderId
               -> m (Maybe (Maybe Id,SrcSpan,Type))
getTypeLHsExpr _ e =
  do hs_env <- getSession
     (_,mbe) <- liftIO (deSugarExpr hs_env e)
     case mbe of
       Nothing -> return Nothing
       Just expr ->
         return (Just (case unwrapVar (unLoc e) of
                         HsVar _ (L _ i) -> Just i
                         _               -> Nothing
                      ,getLoc e
                      ,CoreUtils.exprType expr))
  where
    unwrapVar (HsWrap _ _ var) = var
    unwrapVar e'               = e'

-- | Get id and type for patterns.
getTypeLPat :: (GhcMonad m)
            => TypecheckedModule -> LPat StageReaderId -> m (Maybe (Maybe Id,SrcSpan,Type))
getTypeLPat _ (L spn pat) =
  return (Just (getMaybeId pat,spn,getPatType pat))
  where
    getPatType (ConPatOut (L _ (RealDataCon dc)) _ _ _ _ _ _) =
      dataConRepType dc
    getPatType pat' = hsPatType pat'
    getMaybeId (VarPat _ (L _ vid)) = Just vid
    getMaybeId _                    = Nothing

-- | Get ALL source spans in the source.
listifyAllSpans :: Typeable a
                => TypecheckedSource -> [Located a]
listifyAllSpans tcs =
  listifyStaged TypeChecker p tcs
  where p (L spn _) = isGoodSrcSpan spn

listifyStaged :: Typeable r
              => Stage -> (r -> Bool) -> Data.Generics.GenericQ [r]
listifyStaged _ p = Data.Generics.listify p

------------------------------------------------------------------------------
-- The following was taken from 'ghc-syb-utils'
--
-- ghc-syb-utils:
--     https://github.com/nominolo/ghc-syb

-- | Ghc Ast types tend to have undefined holes, to be filled
--   by later compiler phases. We tag Asts with their source,
--   so that we can avoid such holes based on who generated the Asts.
data Stage
  = Parser
  | Renamer
  | TypeChecker
  deriving (Eq,Ord,Show)

-- | Pretty print the types into a 'SpanInfo'.
toSpanInfo :: (Maybe Id,SrcSpan,Type) -> Maybe SpanInfo
toSpanInfo (n,mspan,typ) =
  case mspan of
    RealSrcSpan spn ->
      Just (SpanInfo (srcSpanStartLine spn)
                     (srcSpanStartCol spn - 1)
                     (srcSpanEndLine spn)
                     (srcSpanEndCol spn - 1)
                     (Just typ)
                     n)
    _ -> Nothing

-- | Pretty print something to string.
showppr :: Outputable a
        => DynFlags -> a -> String
showppr dflags =
  showSDocForUser dflags neverQualify .
  ppr
