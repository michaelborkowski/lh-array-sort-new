{-# language CPP #-}
{-# language OverloadedStrings #-}

-- | GHC plugin to remove friction between Liquid Haskell and Linear Haskell
--
--   Two modes controlled by the plugin arguments (passed by clients via `-fplugin-opt`):
--
--   * linear mode ("linear" is passed)
--   * liquid mode ("liquid" is passed)
--
--   Current effects:
--
--   * if in linear mode, rewrite `a ? b` into `a`.
--     Rationale: the RHS of `?` is for proofs only but leads to spuriuous non-linearity.
--
--   * if in liquid mode, rewrite `Unsafe.toLinear f` to `f`.
--     Rationale: Liquid fails to reflect applications of higher-order functions like
--     `Unsafe.toLinear`, but it's only there to satisfy linearity checker.
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

rewriteQuest :: [CommandLineOption] -> ModSummary -> ParsedResult -> Hsc ParsedResult
rewriteQuest opts _ orig@(ParsedResult m _)
  = do
    dflags <- GHC.getDynFlags
    hpm_module' <- transform opts dflags (GHC.hpm_module m)
    pure $ orig { GHC.parsedResultModule = m { GHC.hpm_module = hpm_module' } }

transform
    :: [CommandLineOption] -- control weather we linear or liquid
    -> GHC.DynFlags
    -> GHC.Located (HsModule GhcPs)
    -> GHC.Hsc (GHC.Located (HsModule GhcPs))
transform opts _dflags = SYB.everywhereM (SYB.mkM (transform' opts))
  where
    transform' :: [CommandLineOption] -> LHsExpr GhcPs -> GHC.Hsc (LHsExpr GhcPs)

    -- case: binary operation `a1 op a2`; check that `op` is `?` and rewrite to `a1` if yes
    -- purpose: remove ? as a source of spurious non-linearity;
    -- mode: linear
    transform' ["linear"] e@(L _ (OpApp _ a1 (L _ (HsVar _ (L _ (Unqual n)))) _a2)) =
      pure $ case occNameString n of
        "?" -> a1
        _   -> e
    -- case: qualified function application `mod.fun arg`; check that `mod.fun` is `Unsafe.toLinear` and
    -- rewrite to `arg` if yes
    -- purpose: remove calls to `toLinear` in the Liquid mode because it breaks Liquid Haskell reflection
    -- mode: liquid
    transform' ["liquid"] e@(L _l (HsApp _ (L _ (HsVar _ (L _ (Qual mod' fun)))) arg)) = do
      case (mod', occNameString fun) of
        (ModuleName "Unsafe", "toLinear") ->
          pure arg
        _          -> pure e

    transform' _ e = do
      pure e
