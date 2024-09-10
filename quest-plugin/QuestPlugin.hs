-- | GHC plugin to rewrite (a ? b) into a
--
module QuestPlugin (plugin) where

import GHC.Plugins as GHC
import GHC.Hs
import GHC

import qualified Data.Generics as SYB

plugin :: Plugin
plugin = defaultPlugin
  { parsedResultAction = rewriteQuest
  , pluginRecompile = purePlugin
  }

rewriteQuest ::[CommandLineOption] -> ModSummary -> ParsedResult -> Hsc ParsedResult
rewriteQuest _ _ orig@(ParsedResult m _)
  = do
    dflags <- GHC.getDynFlags
    hpm_module' <- transform dflags (GHC.hpm_module m)
    pure $ orig { GHC.parsedResultModule = m { GHC.hpm_module = hpm_module' } }

transform
    :: GHC.DynFlags
    -> GHC.Located (HsModule GhcPs)
    -> GHC.Hsc (GHC.Located (HsModule GhcPs))
transform _dflags = SYB.everywhereM (SYB.mkM transform')
  where
    transform' :: LHsExpr GhcPs -> GHC.Hsc (LHsExpr GhcPs)
    transform' e@(L l (OpApp _ o1 (L _ (HsVar _ (L _ (Unqual n)))) o3)) =
      pure $ case occNameString n of
        "?" -> o1
        _   -> e

    transform' e = do
      pure e
