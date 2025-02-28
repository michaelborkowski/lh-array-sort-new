{-# LANGUAGE Strict   #-}

module Main where

import           Data.Int           ( Int64 )
import           System.Random      ( Random, newStdGen, randoms )
import           Data.Proxy         ( Proxy(..) )
import           Control.DeepSeq    ( NFData, force )
import           Data.List.Split    ( splitOn )
import           System.Environment ( getArgs )
import           Control.Monad      ( unless, replicateM )
import           Text.Read
import           Linear.Common
import Types as T

import qualified Data.Primitive.Types as P
import qualified Measure as M
import qualified Insertion as I
import qualified QuickSort as Q
import qualified DpsMergeSort4 as DMS
import qualified DpsMergeSort4Par as DMSP
import qualified PiecewiseFallbackSort as PFS
import qualified PiecewiseFallbackSortPar as PFSP
import qualified Microbench as MB
import qualified Array as A
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Algorithms.Insertion as ISDVS
import qualified Data.Vector.Algorithms.Merge as MSDVS
import qualified Data.Vector.Algorithms.Intro as QSDVS

import Options.Generic

--------------------------------------------------------------------------------

getInput :: Benchmark -> Maybe Int -> IO (Input Int64)
getInput bench mb_size = case bench of
  GenerateArray -> pure $ IntIn (mb 10000000)
  FillArray     -> pure $ EltsIn (mb 10000000) 1024
  CopyArray     -> pure $ ArrayIn (A.make (mb 10000000) 1)
  SumArray      -> pure $ ArrayIn (A.make (mb 10000000) 1)
  Fib           -> pure $ IntIn (mb 45)
  OurSort alg -> case alg of
    Insertionsort -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 100)
    Quicksort     -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 1000000)
    Mergesort     -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 8000000)
    Optsort       -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 8000000)
  _ -> error "getInput: Unexpected Input!"
  where
    mb x = case mb_size of
      Nothing -> x
      Just y  -> y

getInputAsDataVector :: SortAlgo -> Maybe Int -> IO Vec
getInputAsDataVector bench mb_size = case bench of
  Insertionsort -> V.fromList <$> randList (Proxy :: Proxy Int64) (mb 100)
  Quicksort -> V.fromList <$> randList (Proxy :: Proxy Int64) (mb 1000000)
  Mergesort -> V.fromList <$> randList (Proxy :: Proxy Int64) (mb 8000000)
  _ -> error "getInputAsDataVector: TODO sort function not implemented!"
  where
    mb x = case mb_size of
      Nothing -> x
      Just y -> y

getInputAsList :: SortAlgo -> Maybe Int -> IO [Int64]
getInputAsList bench mb_size = case bench of
  Insertionsort -> randList (Proxy :: Proxy Int64) (mb 100)
  Quicksort -> randList (Proxy :: Proxy Int64) (mb 1000000)
  Mergesort -> randList (Proxy :: Proxy Int64) (mb 8000000)
  _ -> error "getInputAsDataVector: TODO sort function not implemented!"
  where
    mb x = case mb_size of
      Nothing -> x
      Just y -> y

copyInput :: (Input Int64) -> IO (Input Int64)
copyInput i = case i of
  ArrayIn arr -> pure $ ArrayIn (A.copy arr 0 (A.make (A.size arr) (A.get arr 0)) 0 (A.size arr))
  _ -> error "TODO: copyInput not implemented!"

copyInputIterTimes :: Input Int64 -> Int -> IO [A.Array Int64]
copyInputIterTimes inp iters = do
  copiedInputs <- replicateM iters (copyInput inp)
  return [arr | ArrayIn arr <- copiedInputs]

randArray :: forall a. (Random a, NFData a, P.Prim a) => Proxy a -> Int -> IO (A.Array a)
randArray _ty size = do
  rng <- newStdGen
  let ls :: [a]
      ls = take size $ randoms rng
      !arr = force (A.fromList ls)
  pure arr

randList :: forall a. (Random a, NFData a) => Proxy a -> Int -> IO [a]
randList _ty size = do
  rng <- newStdGen
  let ls :: [a]
      ls = take size $ randoms rng
  pure (force ls)

sortFn :: (Show a, A.HasPrimOrd a, NFData a) => SortAlgo -> ParOrSeq -> (A.Array a -. A.Array a)
sortFn bench parorseq = case (bench,parorseq) of
  (Insertionsort, Seq) -> I.isort_top'
  (Quicksort, Seq)     -> Q.quickSort'
  (Mergesort, Seq) -> DMS.msort
  (Mergesort, Par) -> DMSP.msort
  (Optsort,   Seq) -> PFS.pfsort
  (Optsort,   Par) -> PFSP.pfsort
  oth -> error $ "sortFn: unknown configuration: " ++ show oth

vectorSortFn :: SortAlgo -> ParOrSeq -> VecSort
vectorSortFn bench parorseq = case (bench,parorseq) of
  (Insertionsort, Seq) -> ISDVS.sort
  (Mergesort,     Seq) -> MSDVS.sort
  (Quicksort,     Seq) -> QSDVS.sort
  oth -> error $ "sortFn: unknown configuration: " ++ show oth

--------------------------------------------------------------------------------

isSorted :: Ord a => [a] -> Bool
isSorted []       = True
isSorted [_]      = True
isSorted (x:y:xs) = x <= y && isSorted (y:xs)

readBench :: String -> Benchmark
readBench s = case readMaybe s of
  Just b -> b
  Nothing -> case readMaybe s of
    Just srt -> OurSort srt
    Nothing -> read s

-- dobench :: Benchmark -> ParOrSeq -> Maybe Int -> IO ()
dobench :: Benchmark -> ParOrSeq -> Maybe Int -> Int -> IO ()
dobench bench parorseq mb_size iters = do
  let
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
      SumArray  -> do
        (ArrayIn arr) <- getInput bench mb_size
        case parorseq of
          Seq -> do
            (res0, tmed0, tall0) <- M.bench MB.sumArray arr iters
            pure (A.size arr, fromIntegral res0, tmed0, tall0)
          Par -> do
            (res0, tmed0, tall0) <- M.bench (MB.sumArray_par 4096) arr iters
            pure (A.size arr, fromIntegral res0, tmed0, tall0)
          _ -> error "dobench: ParM case not expected for SumArray!"
      CopyArray -> do
        (ArrayIn arr) <- getInput bench mb_size
        case parorseq of
          Seq -> do
            let dst = A.make (A.size arr) (A.get arr 0)
            let docopy input = A.copy input 0 dst 0 (A.size arr)
            (res0, tmed0, tall0) <- M.bench docopy arr iters
            unless ((A.toList res0) == (A.toList arr)) (error $ show bench ++ ": result not equal to source.")
            putStrLn "Copied: OK"
            pure (A.size arr, A.size res0, tmed0, tall0)
          Par ->  do
            let dst = A.make (A.size arr) (A.get arr 0)
            let docopy_par input = A.copy_par input 0 dst 0 (A.size arr)
            (res0, tmed0, tall0) <- M.bench docopy_par arr iters
            unless ((A.toList res0) == (A.toList arr)) (error $ show bench ++ ": result not equal to source.")
            putStrLn "Copied: OK"
            pure (A.size arr, A.size res0, tmed0, tall0)
          ParM -> do
            let dst = A.make (A.size arr) (A.get arr 0)
            let docopy_par_m input = A.copy_par_m input 0 dst 0 (A.size arr)
            (res0, tmed0, tall0) <- M.benchPar docopy_par_m arr iters
            unless ((A.toList res0) == (A.toList arr)) (error $ show bench ++ ": result not equal to source.")
            putStrLn "Copied: OK"
            pure (A.size arr, A.size res0, tmed0, tall0)
      VectorSort alg -> do
        inPutVec <- getInputAsDataVector alg mb_size
        let fn = vectorSortFn alg parorseq
        putStrLn $ "array size = " ++ show (V.length inPutVec)
        (res0, tmed0, tall0) <- M.benchAndRunDataVecSorts fn inPutVec iters
        unless (isSorted (V.toList res0)) (error $ show alg ++ ": result not sorted.")
        putStrLn "Sorted: OK"
        pure (V.length inPutVec, V.length res0, tmed0, tall0)
      OurSort alg -> do
        ArrayIn arr <- getInput bench mb_size
        arrs <- copyInputIterTimes (ArrayIn arr) iters
        let fn = sortFn alg parorseq
        putStrLn $ "array size = " ++ show (A.size arr)
        (res0, tmed0, tall0) <- M.benchOnArrays fn arrs
        unless (isSorted (A.toList res0)) (error $ show bench ++ ": result not sorted.")
        putStrLn "Sorted: OK"
        pure (A.size arr, A.size res0, tmed0, tall0)
      CSort alg -> do
        arr <- getInputAsList alg mb_size
        (res0, tmed0, tall0) <- M.benchAndRunCSorts alg arr iters
        unless (isSorted (res0)) (error $ show bench ++ ": result not sorted.")
        putStrLn "Sorted: OK"
        pure (length arr, length res0, tmed0, tall0)
      _ -> error "dobench: case not implemented!"

{-
      FillArray -> do (EltsIn total_elems elt) <- getInput bench mb_size
                      (res0, tmed0, tall0) <- M.bench MB.fillArray (total_elems,elt) iters
                      pure (total_elems, A.size res0, tmed0, tall0)
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
  -- let usage = "USAGE: benchrunner -- BENCH_ARGS -- CRITERION_ARGS"
  let usage = "USAGE: benchrunner ITERS SORT PAR SIZE"
  let (benchmark, parorseq, size, _rst, iters) =
        case splitOn ["--"] allargs of
          -- [] -> (Insertionsort,Seq,Just 10,[])
          -- [(bnch:parorseq0:sz:_)] ->
          --   (read bnch :: Benchmark, read parorseq0 :: ParOrSeq, Just (read sz :: Int), [])
          -- [(bnch:sz:_)] ->
          --   (read bnch :: Benchmark, Seq, Just (read sz :: Int), [])
          -- [(bnch:_)] ->
          --   (read bnch :: Benchmark, Seq, Nothing, [])
          [[its,bnch,md,sz]] -> (readBench bnch, read md :: ParOrSeq, Just (read sz :: Int), [], read its)
          _ -> error usage
  dobench benchmark parorseq size iters
