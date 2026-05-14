{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE Strict #-}

-- | Criterion-based benchmark suite for lh-array-sort.
--
-- Usage:
--   cabal run bench-criterion -- --size N [+criterion-flags+]
--   cabal run bench-criterion -- --size N --csv out.csv
--
-- The --size flag must come before any Criterion flags (i.e., before any '--'
-- separator if used). All remaining arguments are passed to Criterion.
--
-- Algorithms benchmarked: Insertionsort, Mergesort, Quicksort.
-- Contestants per algorithm:
--   ours          - our verified prim-mutable implementation
--   vector        - Data.Vector.Algorithms (unverified Haskell)
--   c             - hand-written C with -O3 (via FFI)
--
-- Example (sequential, single size):
--   cabal run bench-criterion -- --size 1000 --csv bench_1000.csv +RTS -N1
--
-- Example (parallel mergesort at 8M, 4 cores):
--   cabal run bench-criterion -- --size 8000000 --algo MergesortPar --csv par.csv +RTS -N4


-- NOTE: Duplication in this file
--
-- It'd be easy to avoid a lot of duplication in this file (among *SortGroup functions esp.)
-- But it's easy to break  GHC optimizations when you start passing sorting functions around.
-- As a result, we stick with a safer approach of duplicating the benchmark group code for each algorithm.
-- Hopefully, we can fix it one day.

module Main where

import           Control.DeepSeq              ( force )
import           Criterion.Main               ( defaultMainWith, bgroup, bench, perRunEnv, Benchmark )
import           Criterion.Main.Options       ( defaultConfig )
import           Data.Int                     ( Int64 )
import           Data.Maybe                   ( )
import           Foreign                      ( newArray, peekArray, castPtr, sizeOf, Ptr )
import           System.Environment           ( getArgs, withArgs )
import           System.Random                ( newStdGen, randoms )
import           Text.Read                    ( readMaybe )

import qualified Array                        as A
import qualified Data.Vector.Algorithms.Insertion as ISDVS
import qualified Data.Vector.Algorithms.Intro     as QSDVS
import qualified Data.Vector.Algorithms.Merge     as MSDVS
import qualified Data.Vector.Unboxed              as V
import qualified Data.Vector.Unboxed.Mutable      as MV
import qualified ForeignFunctionImports           as FFI
import qualified Insertion                        as I
import qualified QuickSort                        as Q
import qualified DpsMergeSort4                    as DMS
import qualified DpsMergeSort4Par                 as DMSP

--------------------------------------------------------------------------------
-- CLI argument extraction
--------------------------------------------------------------------------------

-- | Extract --size N from the argument list; return (size, remaining_args).
-- Defaults to 1000 if --size is not provided.
extractSize :: [String] -> (Int, [String])
extractSize args = go args []
  where
    go []             acc = (1000, reverse acc)
    go ("--size":n:rest) acc =
      case readMaybe n of
        Just s  -> (s, reverse acc ++ rest)
        Nothing -> error $ "bench-criterion: --size requires an integer, got: " ++ n
    go (x:rest)       acc = go rest (x:acc)

-- | Extract --algo NAME from the argument list; return (algo, remaining_args).
-- Recognised values: Insertionsort, Mergesort, MergesortPar, All (default).
extractAlgo :: [String] -> (String, [String])
extractAlgo args = go args []
  where
    go []              acc = ("All", reverse acc)
    go ("--algo":a:rest) acc = (a, reverse acc ++ rest)
    go (x:rest)        acc = go rest (x:acc)

--------------------------------------------------------------------------------
-- Random input generation
--------------------------------------------------------------------------------

randArray :: Int -> IO (A.Array Int64)
randArray size = do
  rng <- newStdGen
  let !arr = force $ A.fromList (take size (randoms rng :: [Int64]))
  pure arr

randVector :: Int -> IO (V.Vector Int64)
randVector size = do
  rng <- newStdGen
  pure $! force $ V.fromList (take size (randoms rng :: [Int64]))

randList :: Int -> IO [Int64]
randList size = do
  rng <- newStdGen
  pure $! force (take size $ map (`mod` 1000) (randoms rng :: [Int64]))

--------------------------------------------------------------------------------
-- Benchmark groups
--------------------------------------------------------------------------------

-- | Criterion env that provides a fresh A.Array Int64 copy for each trial.
-- Needed because our sorts are linear (they consume the array in-place).
-- Uses perRunEnv so a fresh copy is made each benchmark iteration.
mkArrayEnv :: A.Array Int64 -> IO (A.Array Int64)
mkArrayEnv template =
  let n = A.size template
      !dst = A.make n (A.get template 0)
  in pure $! A.copy template 0 dst 0 n

insertionSortGroup :: Int -> IO [Benchmark]
insertionSortGroup size = do
  templateList <- randList size
  let templateVec = V.fromList templateList
      templateArr = A.fromList templateList

  let grpOurs = bench "ours" $ perRunEnv (mkArrayEnv templateArr) $ \arr -> do
        -- putStrLn $ "Unsort: " ++ show arr
        let !sorted = I.isort_top' arr
        -- putStrLn $ "Sorted: " ++ show sorted
        pure sorted

  let grpVector = bench "vector" $ perRunEnv (V.thaw templateVec) $ \vec -> do
        ISDVS.sort vec
        pure vec

  let grpC = bench "c" $ perRunEnv (newArray templateList) $ \ptr -> do
        sorted <- FFI.c_insertionsort ptr (fromIntegral size)
                    (fromIntegral (sizeOf (undefined :: Int64)))
        pure sorted

  pure [ bgroup ("insertionsort/" ++ show size)
           [ grpOurs, grpVector, grpC ] ]

mergeSortGroup :: Int -> IO [Benchmark]
mergeSortGroup size = do
  templateList <- randList size
  let templateVec = V.fromList templateList
      templateArr = A.fromList templateList

  let grpOurs = bench "ours" $ perRunEnv (mkArrayEnv templateArr) $ \arr -> do
        let !sorted = DMS.msort arr
        pure sorted

  let grpVector = bench "vector" $ perRunEnv (V.thaw templateVec) $ \vec -> do
        MSDVS.sort vec
        pure vec

  let grpC = bench "c" $ perRunEnv (newArray templateList) $ \ptr -> do
        sorted <- FFI.c_mergesort ptr (fromIntegral size)
                    (fromIntegral (sizeOf (undefined :: Int64)))
        pure sorted

  pure [ bgroup ("mergesort/" ++ show size)
           [ grpOurs, grpVector, grpC ] ]

-- | Parallel merge sort (our implementation only; for speedup plots).
mergeSortParGroup :: Int -> IO [Benchmark]
mergeSortParGroup size = do
  templateArr <- randArray size

  let grpOursPar = bench "ours-par" $ perRunEnv (mkArrayEnv templateArr) $ \arr -> do
        let !sorted = DMSP.msort arr
        pure sorted

  pure [ bgroup ("mergesort-par/" ++ show size)
           [ grpOursPar ] ]

quickSortGroup :: Int -> IO [Benchmark]
quickSortGroup size = do
  templateList <- randList size
  let templateVec = V.fromList templateList
      templateArr = A.fromList templateList

  let grpOurs = bench "ours" $ perRunEnv (mkArrayEnv templateArr) $ \arr -> do
        let !sorted = Q.quickSort' arr
        pure sorted

  let grpVector = bench "vector" $ perRunEnv (V.thaw templateVec) $ \vec -> do
        QSDVS.sort vec
        pure vec

  let grpC = bench "c" $ perRunEnv (newArray templateList) $ \ptr -> do
        sorted <- FFI.c_quicksort ptr (fromIntegral size)
                    (fromIntegral (sizeOf (undefined :: Int64)))
        pure sorted

  pure [ bgroup ("quicksort/" ++ show size)
           [ grpOurs, grpVector, grpC ] ]

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

main :: IO ()
main = do
  allArgs <- getArgs
  let (size, afterSize) = extractSize allArgs
      (algo, criterionArgs) = extractAlgo afterSize

  benchmarks <- case algo of
    "Insertionsort" -> insertionSortGroup size
    "Mergesort"     -> mergeSortGroup size
    "MergesortPar"  -> mergeSortParGroup size
    "Quicksort"     -> quickSortGroup size
    "All"           -> do
      is <- insertionSortGroup size
      ms <- mergeSortGroup size
      qs <- quickSortGroup size
      pure (is ++ ms ++ qs)
    other -> error $ "bench-criterion: unknown --algo value: " ++ other
             ++ "\n  Valid values: Insertionsort, Mergesort, MergesortPar, Quicksort, All"

  withArgs criterionArgs $
    defaultMainWith defaultConfig benchmarks
