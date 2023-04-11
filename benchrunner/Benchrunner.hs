{-# LANGUAGE Strict   #-}

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
import qualified Array as A

--------------------------------------------------------------------------------

data Benchmark
  = GenerateArray
  | FillArray
  | CopyArray
  | SumArray
  | Fib
  | Insertionsort
  | Mergesort
  | Quicksort
  | Cilksort
  deriving (Eq, Show, Read)

data ParOrSeq = Seq | Par | ParM
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
  GenerateArray -> pure $ IntIn (mb 10000000)
  FillArray     -> pure $ EltsIn (mb 10000000) 1024
  CopyArray     -> pure $ ArrayIn (A.make (mb 10000000) 1)
  SumArray      -> pure $ ArrayIn (A.make (mb 10000000) 1)
  Fib           -> pure $ IntIn (mb 45)
  Insertionsort -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 100)
  Quicksort     -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 1000000)
  Mergesort     -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 8000000)
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
  -- MergesortPar  -> DMSP.msort

--------------------------------------------------------------------------------

isSorted :: Ord a => [a] -> Bool
isSorted []       = True
isSorted [_]      = True
isSorted (x:y:xs) = x <= y && isSorted (y:xs)


dobench :: Benchmark -> ParOrSeq -> Maybe Int -> IO ()
dobench bench parorseq mb_size = do
  let iters = 9 :: Int
  putStrLn $ "Running " ++ show bench ++ " (" ++ show parorseq ++ ")"
             ++ "\n========================================"
  (size, res, tmed, tall) <-
    case bench of
      Fib -> do
        (IntIn i) <- getInput bench mb_size
        case parorseq of
          Seq -> do
            (res0, tmed0, tall0) <- M.bench MB.seqfib (fromIntegral i) iters
            pure (i, fromIntegral res0, tmed0, tall0)
          Par -> do
            (res0, tmed0, tall0) <- M.bench MB.parfib (fromIntegral i) iters
            pure (i, fromIntegral res0, tmed0, tall0)
          ParM -> do
            (res0, tmed0, tall0) <- M.benchPar MB.parfib1 (fromIntegral i) iters
            pure (i, fromIntegral res0, tmed0, tall0)
      GenerateArray -> do
        (IntIn i) <- getInput bench mb_size
        case parorseq of
          Seq -> do
            let gen n = A.generate n id
            (res0, tmed0, tall0) <- M.bench gen (fromIntegral i) iters
            pure (i, A.size res0, tmed0, tall0)
          Par -> do
            let gen n = A.generate_par n id
            (res0, tmed0, tall0) <- M.bench gen (fromIntegral i) iters
            pure (i, A.size res0, tmed0, tall0)
          ParM -> do
            let gen n = A.generate_par_m n id
            (res0, tmed0, tall0) <- M.benchPar gen (fromIntegral i) iters
            pure (i, A.size res0, tmed0, tall0)
      CopyArray -> do
        (ArrayIn arr) <- getInput bench mb_size
        case parorseq of
          Seq -> do
            let dst = A.make (A.size arr) (A.get arr 0)
            let docopy input = A.copy input 0 dst 0 (A.size arr)
            (res0, tmed0, tall0) <- M.bench docopy arr iters
            pure (A.size arr, A.size res0, tmed0, tall0)
          Par ->  do
            let dst = A.make (A.size arr) (A.get arr 0)
            let docopy_par input = A.copy_par input 0 dst 0 (A.size arr)
            (res0, tmed0, tall0) <- M.bench docopy_par arr iters
            pure (A.size arr, A.size res0, tmed0, tall0)
          ParM -> do
            let dst = A.make (A.size arr) (A.get arr 0)
            let docopy_par_m input = A.copy_par_m input 0 dst 0 (A.size arr)
            (res0, tmed0, tall0) <- M.benchPar docopy_par_m arr iters
            pure (A.size arr, A.size res0, tmed0, tall0)

{-
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
-}
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
  let (benchmark, parorseq, size, _rst) =
        case splitOn ["--"] allargs of
          [] -> (Insertionsort,Seq,Just 10,[])
          [(bnch:parorseq0:sz:_)] ->
            (read bnch :: Benchmark, read parorseq0 :: ParOrSeq, Just (read sz :: Int), [])
          [(bnch:sz:_)] ->
            (read bnch :: Benchmark, Seq, Just (read sz :: Int), [])
          [(bnch:_)] ->
            (read bnch :: Benchmark, Seq, Nothing, [])

          _ -> error usage
  dobench benchmark parorseq size
