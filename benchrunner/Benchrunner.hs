module Main where

import           Data.Int           ( Int64 )
import           System.Random      ( Random, newStdGen, randoms )
import           Data.Proxy         ( Proxy(..) )
import           Control.DeepSeq    ( NFData, force)
import           Data.List.Split    ( splitOn )
import           System.Environment ( getArgs, withArgs )
import           Control.Monad      ( unless )


import qualified Measure as M
import qualified Insertion as I
import qualified DpsMergeSort as DMS
import qualified DpsMergeSort4 as DMS4
import qualified DpsMergeSortPar as DMSP
import qualified DpsMergeSort4Par as DMS4P
import qualified Microbench as MB
import qualified Fib as F
import qualified Array as A

--------------------------------------------------------------------------------

data Benchmark
  = FillArray
  | SumArray
  | Seqfib
  | Seqfib1
  | Parfib
  | Parfib1
  | Insertionsort
  | Mergesort
  | MergesortPar
  | Quicksort
  | Cilksort
  deriving (Eq, Show, Read)

data Input a
  = EltsIn
     Int {- number of elements -}
     a   {- element            -}
  | ArrayIn (A.Array a)
  | IntIn Int
  deriving Show

getInput :: Benchmark -> Maybe Int -> IO (Input Int64)
getInput bench mb_size = case bench of
  FillArray     -> pure $ EltsIn (mb 10000000) 1024
  SumArray      -> pure $ ArrayIn (A.make (mb 10000000) 1)
  Seqfib        -> pure $ IntIn 45
  Seqfib1       -> pure $ IntIn 45
  Parfib        -> pure $ IntIn 45
  Parfib1       -> pure $ IntIn 45
  Insertionsort -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 100)
  Quicksort     -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 1000000)
  Mergesort     -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 8000000)
  MergesortPar  -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 8000000)
  Cilksort      -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 8000000)
  where
    mb x = case mb_size of
      Nothing -> x
      Just y  -> y

randArray :: forall a. (Random a, NFData a) => Proxy a -> Int -> IO (A.Array a)
randArray _ty size = do
  rng <- newStdGen
  let ls :: [a]
      ls = take size $ randoms rng
      !arr = force (A.fromList ls)
  pure arr

sortFn :: (Show a, Ord a, NFData a) => Benchmark -> (A.Array a -> A.Array a)
sortFn bench = case bench of
  Insertionsort -> I.isort_top
  Mergesort     -> DMS.msort
  MergesortPar  -> DMSP.msort

--------------------------------------------------------------------------------

isSorted :: Ord a => [a] -> Bool
isSorted []       = True
isSorted [_]      = True
isSorted (x:y:xs) = x <= y && isSorted (y:xs)


dobench :: Benchmark -> Maybe Int -> IO ()
dobench bench mb_size = do
  let iters = 9 :: Int
  putStrLn $ "Running " ++ show bench ++ "\n========================================"
  (size, res, tmed, tall) <-
    case bench of
      Seqfib    -> do (IntIn i) <- getInput bench mb_size
                      (res0, tmed0, tall0) <- M.bench MB.seqfib (fromIntegral i) iters
                      pure (i, fromIntegral res0, tmed0, tall0)
      Seqfib1   -> do (IntIn i) <- getInput bench mb_size
                      (res0, tmed0, tall0) <- M.bench F.seqfib1 (fromIntegral i) iters
                      pure (i, fromIntegral res0, tmed0, tall0)
      Parfib    -> do (IntIn i) <- getInput bench mb_size
                      (res0, tmed0, tall0) <- M.bench MB.parfib (fromIntegral i) iters
                      pure (i, fromIntegral res0, tmed0, tall0)
      Parfib1   -> do (IntIn i) <- getInput bench mb_size
                      (res0, tmed0, tall0) <- M.benchPar F.parfib1 (fromIntegral i) iters
                      pure (i, fromIntegral res0, tmed0, tall0)
      FillArray -> do (EltsIn total_elems elt) <- getInput bench mb_size
                      (res0, tmed0, tall0) <- M.bench MB.fillArray (total_elems,elt) iters
                      pure (total_elems, A.size res0, tmed0, tall0)
      SumArray  -> do (ArrayIn arr) <- getInput bench mb_size
                      (res0, tmed0, tall0) <- M.bench MB.sumArray arr iters
                      pure (A.size arr, fromIntegral res0, tmed0, tall0)
      _         -> do (ArrayIn arr) <- getInput bench mb_size
                      let fn = sortFn bench
                      putStrLn $ "array size = " ++ show (A.size arr)
                      (res0, tmed0, tall0) <- M.bench fn arr iters
                      unless (isSorted (A.toList res0)) (error $ show bench ++ ": result not sorted.")
                      pure (A.size arr, A.size res0, tmed0, tall0)
  putStrLn $ "BENCHMARK: " ++ show bench
  putStrLn $ "RESULT: " ++ show res
  putStrLn $ "SIZE: " ++ show size
  putStrLn $ "ITERS: " ++ show iters
  putStrLn $ "BATCHTIME: " ++ show tall
  putStrLn $ "SELFTIMED: " ++ show tmed
  putStrLn ""

main :: IO ()
main = do
  allargs <- getArgs
  let usage = "USAGE: benchrunner -- BENCH_ARGS -- CRITERION_ARGS"
      (benchmark, size, _rst) =
        case splitOn ["--"] allargs of
          [] -> (Insertionsort,Just 10,[])
          [(bnch:sz:_)] ->
            if sz == "--help"
            then error usage
            else (read bnch :: Benchmark, Just (read sz :: Int), [])
          [(bnch:_)] -> (read bnch :: Benchmark, Nothing, [])
          [(bnch:sz:_), rst'] ->
            if sz == "--help"
            then error usage
            else (read bnch :: Benchmark, Just (read sz :: Int), rst')
          _ -> error usage
  dobench benchmark size
