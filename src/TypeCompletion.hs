{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}

module TypeCompletion where

#if __GLASGOW_HASKELL__ >= 800
import Module
#endif

#if __GLASGOW_HASKELL__ < 710
import           Data.Foldable (foldMap)
#endif
import           Data.List
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe
import           DynFlags

import           GHC
import           GhcMonad
import           GhciInfo (showppr)
import           GhciTypes
import           Name
import           SrcLoc
import           System.Directory
import           Var
import ConLike
type TypedCandidate = (String,Maybe String)

mkTyThingNameType :: TyThing -> (Name,Maybe Type)
mkTyThingNameType x = case x of
  AnId i -> (getName i, Just $ snd . splitForAllTys $ varType i)
  AConLike (RealDataCon dc) -> (getName dc,Just $ dataConType dc)
  AConLike (PatSynCon psc) -> (getName psc,Nothing)
  ATyCon tc -> (getName tc, Just $ tyConKind tc)
  ACoAxiom _ca -> (getName _ca, Nothing)

findCompletionsWithType :: (GhcMonad m)
                => Map ModuleName ModInfo
                -> FilePath
                -> String
                -> m (Either String [TypedCandidate])
findCompletionsWithType infos fp sample = do
  mname <- guessModule infos fp
  case mname of
    Nothing -> return (Left "Couldn't guess that module name. Does it exist?")
    Just name -> case M.lookup name infos of
      Nothing -> return (Left "No module info for the current file! Try loading it?")
      Just moduleInf -> do
        globalNames <- findGlobalCompletionsWithType sample moduleInf
        localNames  <- findLocalizedCompletionsWithType (modinfoSpans moduleInf) sample
        return (Right (take 50 (nub (localNames ++ globalNames))))

findGlobalCompletionsWithType :: GhcMonad m
  => String
  -> ModInfo
  -> m [TypedCandidate]
findGlobalCompletionsWithType sample moduleInf = do
  df <- getDynFlags
  (qual, ident, minfos) <- splitQualIdentInfo
  let
    toplevelNames = concat (mapMaybe modInfoTopLevelScope minfos)
    filteredToplevels = filter (isPrefixOf ident . showppr df)
                        toplevelNames
  globalNames <- catMaybes <$> mapM (getInfo True) (take 50 filteredToplevels)
  let globalNameTypes = map (\(t,_r,_,_) -> let (n,tt) = mkTyThingNameType t
                                            in (qual ++ showppr df n,fmap (showppr df) tt))
                     globalNames
  return globalNameTypes
  where
    getModInfo qmname = findModule qmname Nothing >>= getModuleInfo
    noQual = ("", sample, [modinfoInfo moduleInf])
    qualSrc = findQualifiedSource
              (map unLoc (modinfoImports moduleInf))
              sample
    splitQualIdentInfo
      | '.' `elem` sample 
      , Just (qual, ident, qualModNames) <- qualSrc = do
          minfos <- catMaybes <$> mapM getModInfo qualModNames
          if null minfos
            then return noQual
            else return (qual, ident, minfos)
      | otherwise = return noQual

-- | Guess a module name from a file path.
guessModule :: GhcMonad m
            => Map ModuleName ModInfo -> FilePath -> m (Maybe ModuleName)
guessModule infos fp =
  do target <- guessTarget fp Nothing
     case targetId target of
       TargetModule mn -> return (Just mn)
       TargetFile fp' _ ->
         case find ((Just fp' ==) .
                    ml_hs_file . ms_location . modinfoSummary . snd)
                   (M.toList infos) of
           Just (mn,_) -> return (Just mn)
           Nothing ->
             do fp'' <- liftIO (makeRelativeToCurrentDirectory fp')
                target' <- guessTarget fp'' Nothing
                case targetId target' of
                  TargetModule mn ->
                    return (Just mn)
                  _ ->
                    case find ((Just fp'' ==) .
                               ml_hs_file . ms_location . modinfoSummary . snd)
                              (M.toList infos) of
                      Just (mn,_) ->
                        return (Just mn)
                      Nothing -> return Nothing

findQualifiedSource :: [ImportDecl n] -> String
                    -> Maybe (String, String, [ModuleName])
findQualifiedSource importDecls sample =
  do (ident,qual) <- breakQual sample
     mnames <- (\nms -> if null nms then Nothing else Just nms)
                 (foldMap (maybeToList . knownAs qual) importDecls)
     return (qual++".", ident, mnames)
  where breakQual xs = case break (== '.') (reverse xs) of
                         (h,_:t) -> Just (reverse h, reverse t)
                         _ -> Nothing
        knownAs qual m
          | qual == moduleNameString name || maybe False (qual ==) (asName m) =
            Just name
          | otherwise = Nothing
          where name = unLoc (ideclName m)
                asName = fmap moduleNameString . ideclAs

-- | Find completions within the local scope of a definition of a
-- module.
findLocalizedCompletionsWithType
  :: GhcMonad m
  => [SpanInfo]
  -> String
  -> m [TypedCandidate]
findLocalizedCompletionsWithType spans' prefix =
  do df <- getDynFlags
     return (mapMaybe (complete df) spans')
  where complete
          :: DynFlags -> SpanInfo -> Maybe TypedCandidate
        complete df si = do
          var <- spaninfoVar si
          let idStr = showppr df var
              tyStr = showppr df <$> spaninfoType si
          if isPrefixOf prefix idStr
            then Just (idStr, tyStr)
            else Nothing
