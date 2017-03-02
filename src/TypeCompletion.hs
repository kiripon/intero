{-# LANGUAGE CPP                      #-}
{-# LANGUAGE OverloadedStrings        #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE ScopedTypeVariables      #-}

module TypeCompletion
  ( findCompletionsWithType
  , Candidate(..)
  ) where

#if __GLASGOW_HASKELL__ >= 800
import           Module           (mkModuleNameFS)
#endif

#if __GLASGOW_HASKELL__ < 710
import           Data.Foldable    (foldMap)
#endif
import           Data.List
import           Data.Map         (Map)
import qualified Data.Map         as M
import           Data.Maybe
import           DynFlags
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except
import Control.Monad.Trans.Maybe
import Control.Monad
import           ConLike
import           GHC
import           GhciInfo         (showppr)
import           GhciTypes
import           GhcMonad
import           System.Directory
import           Var
import Outputable
data Candidate = MkCandidate
  { cId     :: String
  , cType   :: Maybe String
  , cModule :: Maybe String
  } deriving (Show,Eq)

mkTyThingNameType :: TyThing -> (Name,Maybe Type)
mkTyThingNameType x = case x of
  AnId i -> (getName i, Just $ snd . splitForAllTys $ varType i)
  AConLike (RealDataCon dc) -> (getName dc,Just $ dataConType dc)
  AConLike (PatSynCon psc) -> (getName psc,Nothing)
  ATyCon tc -> (getName tc, Just $ tyConKind tc)
  ACoAxiom _coax -> (getName _coax, Nothing)

findCompletionsWithType :: (GhcMonad m)
                => Map ModuleName ModInfo
                -> FilePath
                -> String
                -> ExceptT SDoc m [Candidate]
findCompletionsWithType infos fp sample = do
  mname <- maybeToExceptT "Couldn't guess that module name. Does it exist?" $
           guessModule infos fp
  minfo <- maybeToExceptT "No module info for the current file! Try loading it?" $
           MaybeT . pure $ M.lookup mname infos
  globalNames <- lift $ findGlobalCandidates sample minfo
  localNames  <- lift $ findLocalCandidates (modinfoSpans minfo) sample
  return (take 50 (nub (localNames ++ globalNames)))

findGlobalCandidates :: GhcMonad m
  => String
  -> ModInfo
  -> m [Candidate]
findGlobalCandidates sample moduleInf = do
  df <- getDynFlags
  (qual, ident, minfos) <- splitQualIdentInfo
  let
    toplevelNames = concat (mapMaybe modInfoTopLevelScope minfos)
    filteredToplevels = filter (isPrefixOf ident . showppr df)
                        toplevelNames
  forM (take 20 filteredToplevels) $ \n -> do
    info <- getInfo True n
    case info of
      Nothing -> return $ MkCandidate (showppr df n) Nothing Nothing
      Just (t,_,_,_) -> do
        let (nm,tt) = mkTyThingNameType t
            nm' = showppr df nm
            tt' = showppr df <$> tt
        return $ MkCandidate nm' tt' (Just qual)
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
            => Map ModuleName ModInfo -> FilePath -> MaybeT m ModuleName
guessModule infos fp = do
    target <- lift $ guessTarget fp Nothing
    case targetId target of
        TargetModule mn  -> return mn
        TargetFile fp' _ -> guessModule' fp'
  where
    guessModule' :: GhcMonad m => FilePath -> MaybeT m ModuleName
    guessModule' fp' = case findModByFp fp' of
        Just mn -> return mn
        Nothing -> do
            fp'' <- liftIO (makeRelativeToCurrentDirectory fp')

            target' <- lift $ guessTarget fp'' Nothing
            case targetId target' of
                TargetModule mn -> return mn
                _               -> MaybeT . pure $ findModByFp fp''

    findModByFp :: FilePath -> Maybe ModuleName
    findModByFp fp' = fst <$> find ((Just fp' ==) . mifp) (M.toList infos)
      where
        mifp :: (ModuleName, ModInfo) -> Maybe FilePath
        mifp = ml_hs_file . ms_location . modinfoSummary . snd

findQualifiedSource :: [ImportDecl n] -> String
                    -> Maybe (String, String, [ModuleName])
findQualifiedSource importDecls sample = do
  (ident,qual) <- breakQual sample
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
                asName = fmap moduleNameString . ideclAs

-- | Find completions within the local scope of a definition of a
-- module.
findLocalCandidates
  :: GhcMonad m
  => [SpanInfo]
  -> String
  -> m [Candidate]
findLocalCandidates spans' prefix = do
  df <- getDynFlags
  return (mapMaybe (complete df) spans')
  where
    complete :: DynFlags -> SpanInfo -> Maybe Candidate
    complete df si = do
      var <- spaninfoVar si
      let idStr = showppr df var
          tyStr = showppr df <$> spaninfoType si
      if isPrefixOf prefix idStr
        then Just $! MkCandidate idStr tyStr Nothing
        else Nothing
