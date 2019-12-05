{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE CPP                      #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE ScopedTypeVariables      #-}

-- | Find type/location information.

module GhciFind
  (findType,FindType(..),findLoc,findNameUses,findCompletions,guessModule)
  where

import           Control.Applicative
import           Control.Exception
import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Maybe
import           Data.List
import           Data.Map                   (Map)
import qualified Data.Map                   as M
import           Data.Maybe
import           DynFlags
import           FastString
import           GHC
import           GhciInfo                   (showppr)
import           GhciTypes
import           GhcMonad
import           Intero.Compat
import           Module
import           Name
import           SrcLoc
import           System.Directory
import           Var


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
                         _       -> Nothing
        knownAs qual m
          | qual == moduleNameString name || maybe False (qual ==) (asName m) =
            Just name
          | otherwise = Nothing
          where name = unLoc (ideclName m)
                asName = fmap (moduleNameString . unLoc) . ideclAs

-- | Find completions for the sample, context given by the location.
findCompletions :: (GhcMonad m)
                => Map ModuleName ModInfo
                -> FilePath
                -> String
                -> Int
                -> Int
                -> Int
                -> Int
                -> ExceptT String m [String]
findCompletions infos fp sample sl sc el ec = do
  name <- maybeToExceptT ("Couldn't guess that module name. Does it exist?")
          $ guessModule infos fp
  moduleInf <- maybeToExceptT ("No module info for the current file! Try loading it?")
          $ MaybeT $ return $ M.lookup name infos
  let noQual = ("", sample, [modinfoInfo moduleInf])
      getModInfo qmname = findModule qmname Nothing >>= getModuleInfo
  df <- lift getDynFlags

  ExceptT $ do
    (qual, ident, minfs) <-
      if '.' `notElem` sample
      then return noQual
      else case findQualifiedSource (map unLoc (modinfoImports moduleInf)) sample of
        Nothing -> return noQual
        Just (qual, ident, qualModNames) -> do
          minfos <- catMaybes <$> (mapM getModInfo qualModNames)
          return $ if null minfos
                   then noQual
                   else (qual, ident, minfos)

    let toplevelNames = concat (mapMaybe modInfoTopLevelScope minfs)
        filteredToplevels = map (qual ++)
                          . filter (isPrefixOf ident)
                          . map (showppr df)
                          $ toplevelNames
    localNames <- findLocalizedCompletions (modinfoSpans moduleInf)
                                           sample sl sc el ec
    return (Right (take 30 (nub (localNames ++ filteredToplevels))))

-- | Find completions within the local scope of a definition of a
-- module.
findLocalizedCompletions
  :: GhcMonad m
  => [SpanInfo]
  -> String
  -> Int
  -> Int
  -> Int
  -> Int
  -> m [String]
findLocalizedCompletions spans' prefix _sl _sc _el _ec = do
  df <- getDynFlags
  return (mapMaybe (complete df) spans')
  where complete
          :: DynFlags -> SpanInfo -> Maybe String
        complete df si =
          do var <- spaninfoVar si
             let str = showppr df var
             if isPrefixOf prefix str
               then case getSrcLoc (getName var) of
                      RealSrcLoc {}   -> Just str
                      -- Probably an internally generated name. Ignore it:
                      -- See here: https://github.com/chrisdone/intero/issues/531
                      -- We ignore defered-scope-error names like foo_a8s76
                      UnhelpfulLoc {} -> Nothing
               else Nothing

-- | Find any uses of the given identifier in the codebase.
findNameUses :: (GhcMonad m)
             => Map ModuleName ModInfo
             -> FilePath
             -> String
             -> Int
             -> Int
             -> Int
             -> Int
             -> ExceptT String m [SrcSpan]
findNameUses infos fp string sl sc el ec = do
  name <- maybeToExceptT "Couldn't guess that module name. Does it exist?"
          $ guessModule infos fp
  info <- maybeToExceptT "No module info for the current file! Try loading it?"
          $ MaybeT $ return $ M.lookup name infos
  name' <- findName infos info string sl sc el ec
  df <- lift getSessionDynFlags
  span' <- except $ case getSrcSpan name' of
    UnhelpfulSpan{} ->
      Left $ "Found a name, but no location information. The module is: "
            ++ maybe "<unknown>"
                (showppr df . moduleName)
                (nameModule_maybe name')
    span''          -> Right span''
  return $ stripSurrounding $
    span' : map makeSrcSpan (filter (fromMaybe False
                                        . fmap (reliableNameEquality name')
                                        . fmap getName
                                        . spaninfoVar)
                                    (modinfoSpans info))
  where makeSrcSpan (SpanInfo sl' sc' el' ec' _ _) =
          RealSrcSpan
            (mkRealSrcSpan
               (mkRealSrcLoc (mkFastString fp)
                             sl'
                             (1 + sc'))
               (mkRealSrcLoc (mkFastString fp)
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
        -> FilePath
        -> String
        -> Int
        -> Int
        -> Int
        -> Int
        -> ExceptT String m SrcSpan
findLoc infos fp string sl sc el ec = do
  name <- maybeToExceptT "Couldn't guess that module name. Does it exist?"
          $ guessModule infos fp
  info <- maybeToExceptT "No module info for the current file! Try loading it?"
          $ MaybeT $ return $ M.lookup name infos
  case findImportLoc infos info sl sc el ec of
    Just result -> return result
    Nothing -> do
      name' <- findName infos info string sl sc el ec
      d <- lift $ getSessionDynFlags
      case getSrcSpan name' of
        UnhelpfulSpan{} ->
          throwE ("Found a name, but no location information. The module is: " ++
                        maybe "<unknown>"
                           (showppr d . moduleName)
                           (nameModule_maybe name'))
        span' -> return span'

findImportLoc :: (Map ModuleName ModInfo) -> ModInfo -> Int -> Int -> Int -> Int -> Maybe SrcSpan
findImportLoc infos info sl sc el ec =
  do importedModuleName <- getModuleImportedAt info sl sc el ec
     importedModInfo <- M.lookup importedModuleName infos
     return (modinfoLocation importedModInfo)

getModuleImportedAt :: ModInfo -> Int -> Int -> Int -> Int -> Maybe ModuleName
getModuleImportedAt info sl sc el ec = fmap (unLoc . ideclName . unLoc) importDeclarationMaybe
  where importDeclarationMaybe = listToMaybe $ filter isWithinRange (modinfoImports info)
        isWithinRange importDecl = containsSrcSpan sl sc el ec (getLoc $ ideclName $ unLoc importDecl)

-- | Try to resolve the name located at the given position, or
-- otherwise resolve based on the current module's scope.
findName :: GhcMonad m
         => Map ModuleName ModInfo
         -> ModInfo
         -> String
         -> Int
         -> Int
         -> Int
         -> Int
         -> ExceptT String m Name
findName infos mi string sl sc el ec =
  case resolveName (modinfoSpans mi)
                   sl
                   sc
                   el
                   ec of
    Nothing -> tryExternalModuleResolution
    Just name ->
      case getSrcSpan name of
        UnhelpfulSpan{} -> tryExternalModuleResolution
        _               -> return (getName name)
  where tryExternalModuleResolution =
          case find (matchName string)
                    (fromMaybe [] (modInfoTopLevelScope (modinfoInfo mi))) of
            Nothing -> throwE "Couldn't resolve to any modules."
            Just imported -> resolveNameFromModule infos imported
        matchName :: String -> Name -> Bool
        matchName str name =
          str ==
          occNameString (getOccName name)

-- | Try to resolve the name from another (loaded) module's exports.
resolveNameFromModule :: GhcMonad m
                      => Map ModuleName ModInfo
                      -> Name
                      -> ExceptT String m Name
resolveNameFromModule infos name = do
  d <- lift getSessionDynFlags
  modL <- maybeToExceptT ("No module for " ++ showppr d name)
          $ MaybeT $ return $ nameModule_maybe name
  info <- maybeToExceptT (unitIdString (moduleUnitId modL) ++ ":" ++ showppr d modL)
          $ MaybeT $ return $ M.lookup (moduleName modL) infos
  case find (reliableNameEquality name)
            (modInfoExports (modinfoInfo info)) <|>
       find (reliableNameEquality name)
            (fromMaybe [] (modInfoTopLevelScope (modinfoInfo info))) of
    Just name' -> return name'
    Nothing -> do
      maybeToExceptT ("No matching export in any local modules: " ++ showppr d name)
        $ fmap getName $ MaybeT $ lookupGlobalName name

-- | Try to resolve the type display from the given span.
resolveName :: [SpanInfo] -> Int -> Int -> Int -> Int -> Maybe Var
resolveName spans' sl sc el ec =
  listToMaybe (mapMaybe spaninfoVar (filter inside (reverse spans')))
  where inside (SpanInfo sl' sc' el' ec' _ _) =
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
         -> FilePath
         -> String
         -> Int
         -> Int
         -> Int
         -> Int
         -> ExceptT String m FindType
findType infos fp string sl sc el ec = do
  modName <- maybeToExceptT ("Couldn't guess that module name. Does it exist?")
          $ guessModule infos fp
  minfo <- maybeToExceptT ("Couldn't guess the module name. Is this module loaded?")
          $ MaybeT $ return $ M.lookup modName infos
  names <- lift $ lookupNamesInContext string
  let !mspaninfo = resolveSpanInfo (modinfoSpans minfo)
                   sl
                   sc
                   el
                   ec
  lift $ do
    case mspaninfo of
      Just si
        | Just ty <- spaninfoType si -> do
          case fmap Var.varName (spaninfoVar si) of
            Nothing -> return (FindType minfo ty)
            Just name ->
              case find (reliableNameEquality name) names of
                Nothing -> return (FindType minfo ty)
                Just nameWithBetterType -> do
                  result <- ghc_getInfo True nameWithBetterType
                  return $ case result of
                    Nothing            -> FindType minfo ty
                    Just (thing,_,_,_) -> FindTyThing minfo thing
      _ ->
        fmap (FindType minfo)
             (exprType TM_Inst string)

-- | Try to resolve the type display from the given span.
resolveSpanInfo :: [SpanInfo] -> Int -> Int -> Int -> Int -> Maybe SpanInfo
resolveSpanInfo spanList spanSL spanSC spanEL spanEC =
  listToMaybe
    (sortBy (flip compareSpanInfoStart)
            (filter (containsSpanInfo spanSL spanSC spanEL spanEC) spanList))

-- | Compare the start of two span infos.
compareSpanInfoStart :: SpanInfo -> SpanInfo -> Ordering
compareSpanInfoStart this that =
  case compare (spaninfoStartLine this) (spaninfoStartLine that) of
    EQ -> compare (spaninfoStartCol this) (spaninfoStartCol that)
    c  -> c

-- | Does the 'SpanInfo' contain the location given by the Ints?
containsSpanInfo :: Int -> Int -> Int -> Int -> SpanInfo -> Bool
containsSpanInfo spanSL spanSC spanEL spanEC (SpanInfo ancestorSL ancestorSC ancestorEL ancestorEC _ _) =
  contains spanSL spanSC spanEL spanEC ancestorSL ancestorSC ancestorEL ancestorEC

containsSrcSpan :: Int -> Int -> Int -> Int -> SrcSpan -> Bool
containsSrcSpan spanSL spanSC spanEL spanEC (RealSrcSpan spn) =
  contains spanSL spanSC spanEL spanEC (srcSpanStartLine spn) (srcSpanStartCol spn - 1) (srcSpanEndLine spn) (srcSpanEndCol spn - 1)
containsSrcSpan _ _ _ _ _ = False

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
    findModByFp :: Monad m => FilePath -> MaybeT m ModuleName
    findModByFp fp' = MaybeT . return $ fst <$> find ((Just fp' ==) . mifp) (M.toList infos)

    mifp :: (ModuleName, ModInfo) -> Maybe FilePath
    mifp = ml_hs_file . ms_location . modinfoSummary . snd

    guessModule' :: GhcMonad m => FilePath -> MaybeT m ModuleName
    guessModule' fp' = findModByFp fp' <|> do
      fp'' <- liftIO $ makeRelativeToCurrentDirectory fp'
      target' <- lift $ guessTarget fp'' Nothing
      case targetId target' of
        TargetModule mn -> return mn
        _               -> findModByFp fp''

-- | Lookup the name of something in the current context.
lookupNamesInContext :: GhcMonad m => String -> m [Name]
lookupNamesInContext string =
  gcatch (GHC.parseName string)
         (\(_ :: SomeException) -> return [])
