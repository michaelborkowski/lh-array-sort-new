module Main where

import           Criterion          ( Benchmark, bench, bgroup, whnf, nf )
import           Criterion.Main     ( defaultMain )
import           Control.DeepSeq    ( NFData, force)
import           Control.Monad      ( forM_, unless )
import           Data.Proxy         ( Proxy(..) )
import           Data.Int           ( Int64 )
import           Data.List.Split    ( splitOn )
import           System.Random      ( Random, newStdGen, randoms )
import           System.Environment ( getArgs, withArgs )
import qualified Measure as M

import qualified Insertion as I
-- import qualified QuickSort as Q
-- import qualified Merge as M
import qualified DpsMergeSort as DMS
import qualified DpsMergeSort4 as DMS4
import qualified DpsMergeSortPar as DMSP
import qualified DpsMergeSort4Par as DMS4P
import qualified Microbench as MB
-- import qualified CilkSort as C
import qualified Array as A

--------------------------------------------------------------------------------
-- Criterion benchmarks
--------------------------------------------------------------------------------

benchSorts :: forall a. (Random a, NFData a, Ord a) =>
              Proxy a -> Int -> [(String, A.Array a -> A.Array a)] -> IO Benchmark
benchSorts _input_ty input_size fns = do
    rng <- newStdGen
    let ls :: [a]
        ls = take input_size $ randoms rng
        !input = force (A.fromList ls)
    forM_ fns $ \(name,fn) ->
      unless (isSorted (A.toList $ fn input)) (error $ name ++ ": result not sorted.")
    pure $ bgroup "" $ map (go input (show input_size)) fns
  where
    go input str (name,fn) = bench (name ++ "/" ++ str) (nf fn input)

    isSorted :: Ord a => [a] -> Bool
    isSorted []       = True
    isSorted [_]      = True
    isSorted (x:y:xs) = x <= y && isSorted (y:xs)

bench_fill_array :: Int -> IO Benchmark
bench_fill_array input_size = do
  let input :: (Int, Int)
      !input = force (input_size, 1000)
  pure $ bgroup "" [ bench "fill_array" (nf fill input) ]
  where
    fill (s,x) = A.make s x

bench_sum_array :: forall a. (Random a, NFData a, Num a) =>
                   Proxy a -> Int -> IO Benchmark
bench_sum_array _input_ty input_size = do
  rng <- newStdGen
  let ls :: [a]
      ls = take input_size $ randoms rng
      !input = force (A.fromList ls)
  pure $ bgroup "" [ bench "sum_array" (nf sum_array input) ]

--------------------------------------------------------------------------------
-- Non-criterion benchmarks
--------------------------------------------------------------------------------

benchSorts_nocriterion ::
  forall a. (Show a, Random a, NFData a, Ord a) =>
  Proxy a -> Int -> [(String, A.Array a -> A.Array a)] -> IO ()
benchSorts_nocriterion _input_ty input_size fns = do
    rng <- newStdGen
    let ls :: [a]
        ls = take input_size $ randoms rng
        !input = force (A.fromList ls)

    forM_ fns $ \(name,fn) -> do
      unless (isSorted (A.toList $ fn input)) (error $ name ++ ": result not sorted.")
      putStrLn $ "BENCHMARK: " ++ name
      (res0, t0, t_all) <- M.bench fn input 9
      putStrLn $ "SIZE: " ++ show input_size
      putStrLn $ "ITERS: " ++ show 9
      putStrLn $ "BATCHTIME: " ++ show t_all
      putStrLn $ "SELFTIMED: " ++ show t0
      putStrLn ""
  where
    go input str (name,fn) = bench (name ++ "/" ++ str) (nf fn input)
    isSorted :: Ord a => [a] -> Bool
    isSorted []       = True
    isSorted [_]      = True
    isSorted (x:y:xs) = x <= y && isSorted (y:xs)

bench_fill_array_nocriterion :: Int -> IO ()
bench_fill_array_nocriterion input_size = do
  let input :: (Int, Int)
      !input = force (input_size, 1000)
  putStrLn $ "BENCHMARK: " ++ "fill array"
  (res0, t0, t_all) <- M.bench fill input 9
  putStrLn $ "SIZE: " ++ show input_size
  putStrLn $ "ITERS: " ++ show 9
  putStrLn $ "BATCHTIME: " ++ show t_all
  putStrLn $ "SELFTIMED: " ++ show t0
  putStrLn ""
  where
    fill (s,x) = A.make s x

bench_sum_array_nocriterion ::
  forall a. (Show a, Random a, NFData a, Num a) =>
  Proxy a -> Int -> IO ()
bench_sum_array_nocriterion _input_ty input_size = do
  rng <- newStdGen
  let ls :: [a]
      ls = take input_size $ randoms rng
      !input = force (A.fromList ls)
  putStrLn $ "BENCHMARK: " ++ "sum array"
  (res0, t0, t_all) <- M.bench sum_array input 9
  putStrLn $ "SIZE: " ++ show input_size
  putStrLn $ "ITERS: " ++ show 9
  putStrLn $ "BATCHTIME: " ++ show t_all
  putStrLn $ "SELFTIMED: " ++ show t0
  putStrLn ""

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------

data Benchmarks = FillArray | SumArray | Insertionsort | Mergesort | Quicksort | Cilksort
  deriving (Eq, Show, Read)

main :: IO ()
main = do
  allargs <- getArgs
  let usage = "USAGE: benchrunner -- BENCH_ARGS -- CRITERION_ARGS"
      (benchmark,size,rst) =
        case splitOn ["--"] allargs of
          [] -> (Insertionsort,10,[])
          [(bnch:sz:_)] -> if sz == "--help"
                      then error usage
                      else (read bnch :: Benchmarks, read sz :: Int, [])
          [(bnch:sz:_), rst'] -> if sz == "--help"
                            then error usage
                            else (read bnch :: Benchmarks, read sz :: Int, rst')
          _ -> error usage

  runbench <-
    case benchmark of
      FillArray -> do
        bench_fill_array_nocriterion size
        bench_fill_array size
      SumArray  -> do
        bench_sum_array_nocriterion (Proxy :: Proxy Int64) size
        bench_sum_array (Proxy :: Proxy Int64) size
      Insertionsort -> do
        benchSorts_nocriterion
          (Proxy :: Proxy Int64)
          size
          [ ("LH/insertion", I.isort_top) ]

        benchSorts
          (Proxy :: Proxy Int64)
          size
          [ ("LH/insertion", I.isort_top) ]
      Mergesort -> do
        benchSorts_nocriterion
                (Proxy :: Proxy Float)
                size
                [
                  ("LH/dps_mergesort", DMS.msort)
                , ("LH/dps_mergesort_4way", DMS4.msort)
                , ("LH/dps_mergesort_parallel", DMSP.msort)
                , ("LH/dps_mergesort_4way_parallel", DMS4P.msort)
                ]

        benchSorts
                (Proxy :: Proxy Float)
                size
                [
                  ("LH/dps_mergesort", DMS.msort)
                , ("LH/dps_mergesort_4way", DMS4.msort)
                , ("LH/dps_mergesort_parallel", DMSP.msort)
                , ("LH/dps_mergesort_4way_parallel", DMS4P.msort)
                ]
                -- [ ("LH/dps_merge", DM.msort) ]
{-
      Quicksort ->
        benchSorts
                (Proxy :: Proxy Float)
                size
                [ ("LH/quickSort", Q.quickSort) ]
      Cilksort ->
        benchSorts
                (Proxy :: Proxy Float)
                size
                [ ("LH/cilkSort", C.cilkSort) ]
-}
  withArgs rst $ defaultMain [ runbench ]
