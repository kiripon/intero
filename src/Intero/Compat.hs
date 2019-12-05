{-# LANGUAGE CPP #-}

-- | Compatibility between GHC API versions.

module Intero.Compat
  ( ghc_getModuleGraph
  , ghc_getInfo
  , ghc_defaultDynFlags
  , ghc_topSortModuleGraph
  , ghc_mkWarn
  , ghc_mkErr
  , ghc_errMsg
  , ghc_warnMsg
  , ghc_tyConFlavour
  , StageReaderName
  , StageReaderRdrName
  , StageReaderId
  ) where

import           TyCoRep
import           TyCon
import           CmdLineParser
import qualified Data.Graph as SCC
import           DynFlags
import           GHC

ghc_tyConFlavour :: TyCon -> String
ghc_tyConFlavour n =
  if tyConFlavour n == ClassFlavour
    then "class"
    else ""

ghc_defaultDynFlags :: Settings -> DynFlags
ghc_defaultDynFlags s = defaultDynFlags s mempty

ghc_getInfo :: GhcMonad m => Bool -> Name -> m (Maybe (TyThing, Fixity, [ClsInst], [FamInst]))
ghc_getInfo x y = fmap (fmap (\(a,b,c,d,_) -> (a,b,c,d))) (getInfo x y)

ghc_getModuleGraph :: GhcMonad m => m [ModSummary]
ghc_getModuleGraph = fmap mgModSummaries GHC.getModuleGraph

ghc_topSortModuleGraph :: Bool -> [ModSummary] -> Maybe ModuleName -> [SCC.SCC ModSummary]
ghc_topSortModuleGraph bool sums may = GHC.topSortModuleGraph bool (mkModuleGraph sums) may

type StageReaderName = GhcRn

type StageReaderRdrName = GhcPs

type StageReaderId = GhcTc

ghc_mkWarn :: Located String -> Warn
ghc_mkWarn = Warn CmdLineParser.NoReason

ghc_mkErr :: Located String -> Err
ghc_mkErr = Err

ghc_errMsg :: Err -> Located String
ghc_errMsg = errMsg

ghc_warnMsg :: Warn -> Located String
ghc_warnMsg = warnMsg
