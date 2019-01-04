{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}

-- | Find type/location information.

module GhciFind
  (findType,FindType(..),findLoc,findNameUses,findCompletions,guessModule, MyRealSrcSpan(..))
  where

import           Intero.Compat
#if __GLASGOW_HASKELL__ >= 800
import           Module
#endif
import           Control.Exception
#if __GLASGOW_HASKELL__ < 710
import           Data.Foldable (foldMap)
#endif
import           Data.List
import           Data.Map (Map)
import qualified Data.Map as M
import           Data.Maybe
import           DynFlags
import           FastString
import           GHC
import           GhcMonad
import           GhciInfo (showppr)
import           GhciTypes
import           Name
import           Outputable
import           SrcLoc
import           System.Directory
import           Var
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Except
import           Control.Applicative

-- | Check if there is are imported modules that should be searched
-- for the completion sample string. If so, returns the name qualifier
-- (i.e. module name or alias), the identifier prefix to search for,
-- and the `ModuleName`s of the modules in which to search.
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
#if __GLASGOW_HASKELL__ >= 802
                asName = fmap (moduleNameString . unLoc) . ideclAs
#else
                asName = fmap moduleNameString . ideclAs
#endif
data MyRealSrcSpan = MyRealSrcSpan FilePath Int Int Int Int
-- | Find completions for the sample, context given by the location.
findCompletions :: (GhcMonad m)
                => Map ModuleName ModInfo
                -> RealSrcSpan
                -> String
                -> ExceptT SDoc m [String]
findCompletions infos span0 sample =
  do name <- maybeToExceptT (text "Couldn't guess that module name. Does it exist?") $
             guessModule infos (srcSpanFilePath span0)

     info <- maybeToExceptT (text "No module info for the current file! Try loading it?") $
             MaybeT $ return $ M.lookup name infos

     df <- lift getDynFlags
     (qual, ident, minfs) <-
        let noQual = ("", sample, [modinfoInfo info])
            getModInfo qmname =
              findModule qmname Nothing >>= getModuleInfo
        in if '.' `elem` sample
           then case findQualifiedSource
                        (map unLoc (modinfoImports info))
                        sample of
                   Just (qual, ident, qualModNames) -> do
                     minfos <- lift $ fmap catMaybes
                                    (mapM getModInfo qualModNames)
                     if null minfos
                        then return noQual
                        else return (qual, ident, minfos)
                   Nothing -> return noQual
           else return noQual
     let toplevelNames = concat (mapMaybe modInfoTopLevelScope minfs)
         filteredToplevels =
           map (qual ++)
               (filter (isPrefixOf ident)
                       (map (showppr df) toplevelNames))
     localNames <- lift $ findLocalizedCompletions (modinfoSpans info)
                                            sample span0
     return (take 30 (nub (localNames ++ filteredToplevels)))

-- | Find completions within the local scope of a definition of a
-- module.
findLocalizedCompletions
  :: GhcMonad m
  => [SpanInfo]
  -> String
  -> RealSrcSpan
  -> m [String]
findLocalizedCompletions spans' prefix _span =
  do df <- getDynFlags
     return (mapMaybe (complete df) spans')
  where complete
          :: DynFlags -> SpanInfo -> Maybe String
        complete df si =
          do var <- spaninfoVar si
             let str = showppr df var
             if isPrefixOf prefix str
                then Just str
                else Nothing

-- | Find any uses of the given identifier in the codebase.
findNameUses :: (GhcMonad m)
             => Map ModuleName ModInfo
             -> RealSrcSpan
             -> String
             -> ExceptT SDoc m [SrcSpan]
findNameUses infos span0 string =
  do name <- maybeToExceptT (text "Couldn't guess that module name. Does it exist?") $
             guessModule infos (srcSpanFilePath span0)

     info <- maybeToExceptT (text "No module info for the current file! Try loading it?") $
             MaybeT $ pure $ M.lookup name infos

     name' <- findName infos info string span0
     case getSrcSpan name' of
       UnhelpfulSpan{} ->
         do throwE (text "Found a name, but no location information. The module is: " <>
                          maybe (text "<unknown>")
                                (ppr . moduleName)
                                (nameModule_maybe name'))
       span' ->
         return (stripSurrounding
                          (span' :
                           map makeSrcSpan
                               (filter (fromMaybe False .
                                        fmap (reliableNameEquality name') .
                                        fmap getName .
                                        spaninfoVar)
                                       (modinfoSpans info))))
  where makeSrcSpan (SpanInfo sl' sc' el' ec' _ _) =
          RealSrcSpan
            (mkRealSrcSpan
               (mkRealSrcLoc (mkFastString $ srcSpanFilePath span0)
                             sl'
                             (1 + sc'))
               (mkRealSrcLoc (mkFastString $ srcSpanFilePath span0)
                             el'
                             (1 + ec')))

-- | Reliable equality for two names. This tests based on the start
-- line and start column and module.
--
-- We don't use standard equality. The unique can differ. Even the end
-- column can differ.
reliableNameEquality :: Name -> Name -> Bool
reliableNameEquality name1 name2 = nameSrcLoc name1 == nameSrcLoc name2

-- | Strip out spans which surrounding other spans in a parent->child
-- fashion. Those are useless.
stripSurrounding :: [SrcSpan] -> [SrcSpan]
stripSurrounding xs =
  mapMaybe (\x -> if any (\y -> overlaps x y && x /= y) xs
                     then Nothing
                     else Just x)
           xs

-- | Does x overlap y in x `overlaps` y?
overlaps :: SrcSpan -> SrcSpan -> Bool
overlaps y x =
  case (x,y) of
    (RealSrcSpan x',RealSrcSpan y') ->
      realSrcSpanStart y' <= realSrcSpanStart x' &&
      realSrcSpanEnd y' >= realSrcSpanEnd x'
    _ -> False

-- | Try to find the location of the given identifier at the given
-- position in the module.
findLoc :: (GhcMonad m)
        => Map ModuleName ModInfo
        -> RealSrcSpan
        -> String
        -> ExceptT SDoc m SrcSpan
findLoc infos span0 string =
  do name <- maybeToExceptT (text "Couldn't guess that module name. Does it exist?") $
             guessModule infos (srcSpanFilePath span0)

     info <- maybeToExceptT (text "No module info for the current file! Try loading it?") $
             MaybeT $ pure $ M.lookup name infos

     case findImportLoc infos info span0 of
       Just result -> return result
       Nothing ->
         do name' <- findName infos info string span0
            case getSrcSpan name' of
              UnhelpfulSpan{} ->
                throwE (text "Found a name, but no location information. The module is:" <+>
                              maybe (text "<unknown>")
                                 (ppr . moduleName)
                                 (nameModule_maybe name'))

              span' -> return span'

findImportLoc :: (Map ModuleName ModInfo) -> ModInfo -> RealSrcSpan -> Maybe SrcSpan
findImportLoc infos info span0 =
  do importedModuleName <- getModuleImportedAt info span0
     importedModInfo <- M.lookup importedModuleName infos
     return (modinfoLocation importedModInfo)

getModuleImportedAt :: ModInfo -> RealSrcSpan -> Maybe ModuleName
getModuleImportedAt info span0 = fmap (unLoc . ideclName . unLoc) importDeclarationMaybe
  where importDeclarationMaybe = listToMaybe $ filter isWithinRange (modinfoImports info)
        isWithinRange importDecl = containsSrcSpan span0 (getLoc $ ideclName $ unLoc importDecl)

-- | Try to resolve the name located at the given position, or
-- otherwise resolve based on the current module's scope.
findName :: GhcMonad m
         => Map ModuleName ModInfo
         -> ModInfo
         -> String
         -> RealSrcSpan
         -> ExceptT SDoc m Name
findName infos mi string span0 =
  case resolveName (modinfoSpans mi) span0 of
    Nothing -> tryExternalModuleResolution
    Just name ->
      case getSrcSpan name of
        UnhelpfulSpan{} -> tryExternalModuleResolution
        _ -> return (getName name)
  where tryExternalModuleResolution =
          case find (matchName string)
                    (fromMaybe [] (modInfoTopLevelScope (modinfoInfo mi))) of
            Nothing -> throwE $ text "Couldn't resolve to any modules."
            Just imported -> resolveNameFromModule infos imported
        matchName :: String -> Name -> Bool
        matchName str name =
          str ==
          occNameString (getOccName name)

-- | Try to resolve the name from another (loaded) module's exports.
resolveNameFromModule :: GhcMonad m
                      => Map ModuleName ModInfo
                      -> Name
                      -> ExceptT SDoc m Name
resolveNameFromModule infos name =
  do modL <- maybe (throwE $ text "No module for" <+> ppr name) return $
             nameModule_maybe name
     info <- maybe (throwE $ ppr modL) return $
             M.lookup (moduleName modL) infos
     maybeToExceptT (text "No matching export in any local modules:" <+> ppr name) $
             (MaybeT $ return $ find (reliableNameEquality name) (modInfoExports (modinfoInfo info)))
         <|> (MaybeT $ return $ find (reliableNameEquality name) (fromMaybe [] (modInfoTopLevelScope (modinfoInfo info))))
         <|> getName <$> (MaybeT $ lookupGlobalName name)

-- | Try to resolve the type display from the given span.
resolveName :: [SpanInfo] -> RealSrcSpan -> Maybe Var
resolveName spans' span0 =
  listToMaybe (mapMaybe spaninfoVar (filter inside (reverse spans')))
  where
    sl = srcSpanStartLine span0
    sc = srcSpanStartCol span0
    el = srcSpanEndLine span0
    ec = srcSpanEndCol span0
    inside (SpanInfo sl' sc' el' ec' _ _) =
          ((sl' == sl && sc' >= sc) || (sl' > sl)) &&
          ((el' == el && ec' <= ec) || (el' < el))

data FindType
  = FindType ModInfo
             Type
  | FindTyThing ModInfo
                TyThing

-- | Try to find the type of the given span.
findType :: GhcMonad m
         => Map ModuleName ModInfo
         -> RealSrcSpan
         -> String
         -> ExceptT SDoc m FindType
findType infos span0 string =
  do modName <- maybeToExceptT (text "Couldn't guess that module name. Does it exist?") $
                guessModule infos (srcSpanFilePath span0)

     minfo   <- maybeToExceptT (text "Couldn't guess the module name. Is this module loaded?") $
                MaybeT $ return $ M.lookup modName infos

     names <- lift $ lookupNamesInContext string
     let !mspaninfo = resolveSpanInfo (modinfoSpans minfo) span0
     case mspaninfo of
       Just si
         | Just ty <- spaninfoType si ->
           case fmap Var.varName (spaninfoVar si) of
             Nothing -> return (FindType minfo ty)
             Just name ->
               case find (reliableNameEquality name) names of
                 Just nameWithBetterType ->
                   do result <- lift $ ghc_getInfo True nameWithBetterType
                      case result of
                        Just (thing,_,_,_) ->
                          return (FindTyThing minfo thing)
                        Nothing -> return (FindType minfo ty)
                 Nothing -> return (FindType minfo ty)
       _ ->
         fmap (FindType minfo)
#if __GLASGOW_HASKELL__ >= 802
                  (lift $ exprType TM_Inst string)
#else
                  (lift $ exprType string)
#endif

-- | Try to resolve the type display from the given span.
resolveSpanInfo :: [SpanInfo] -> RealSrcSpan -> Maybe SpanInfo
resolveSpanInfo spanList span0 =
    let spanSL = srcSpanStartLine span0
        spanSC = srcSpanStartCol span0
        spanEL = srcSpanEndLine span0
        spanEC = srcSpanEndCol span0
    in listToMaybe
       (sortBy (flip compareSpanInfoStart)
        (filter (containsSpanInfo spanSL spanSC spanEL spanEC) spanList))

-- | Compare the start of two span infos.
compareSpanInfoStart :: SpanInfo -> SpanInfo -> Ordering
compareSpanInfoStart this that =
  case compare (spaninfoStartLine this) (spaninfoStartLine that) of
    EQ -> compare (spaninfoStartCol this) (spaninfoStartCol that)
    c -> c

-- | Does the 'SpanInfo' contain the location given by the Ints?
containsSpanInfo :: Int -> Int -> Int -> Int -> SpanInfo -> Bool
containsSpanInfo spanSL spanSC spanEL spanEC (SpanInfo ancestorSL ancestorSC ancestorEL ancestorEC _ _) =
  contains spanSL spanSC spanEL spanEC ancestorSL ancestorSC ancestorEL ancestorEC

containsSrcSpan :: RealSrcSpan -> SrcSpan -> Bool
containsSrcSpan span0 (RealSrcSpan spn) =
  let spanSL = srcSpanStartLine span0
      spanSC = srcSpanStartCol span0
      spanEL = srcSpanEndLine span0
      spanEC = srcSpanEndCol span0
  in contains spanSL spanSC spanEL spanEC (srcSpanStartLine spn) (srcSpanStartCol spn - 1) (srcSpanEndLine spn) (srcSpanEndCol spn - 1)
containsSrcSpan _ _ = False

contains :: Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Bool
contains spanSL spanSC spanEL spanEC ancestorSL ancestorSC ancestorEL ancestorEC =
  ((ancestorSL == spanSL && spanSC >= ancestorSC) || (ancestorSL < spanSL)) &&
  ((ancestorEL == spanEL && spanEC <= ancestorEC) || (ancestorEL > spanEL))

-- | Guess a module name from a file path.
guessModule :: GhcMonad m
            => Map ModuleName ModInfo -> FilePath -> MaybeT m ModuleName
guessModule infos fp = do
    target <- lift $ guessTarget fp Nothing
    case targetId target of
        TargetModule mn  -> return mn
        TargetFile fp' _ -> guessModule' fp'
  where
    guessModule' fp' = findModByFp fp' <|> do
        fp'' <- liftIO (makeRelativeToCurrentDirectory fp')
        target' <- lift $ guessTarget fp'' Nothing
        case targetId target' of
          TargetModule mn -> return mn
          _               -> findModByFp fp''
    findModByFp :: Monad m => FilePath -> MaybeT m ModuleName
    findModByFp fp' = MaybeT . return $ fst <$> find ((Just fp' ==) . mifp) (M.toList infos)
    mifp :: (ModuleName, ModInfo) -> Maybe FilePath
    mifp = ml_hs_file . ms_location . modinfoSummary . snd

-- | Lookup the name of something in the current context.
lookupNamesInContext :: GhcMonad m => String -> m [Name]
lookupNamesInContext string =
  gcatch (GHC.parseName string)
         (\(_ :: SomeException) -> return [])

-- | Convenience wrapper around 'srcSpanFile' which results in a 'FilePath'
srcSpanFilePath :: RealSrcSpan -> FilePath
srcSpanFilePath = unpackFS . srcSpanFile
