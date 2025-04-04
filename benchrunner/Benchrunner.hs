{-# LANGUAGE Strict   #-}

module Main where

import           Data.List.Split    ( splitOn )
import           System.Environment ( getArgs )
import           Control.Monad      ( unless )

import qualified Array as A
import qualified Vector as V
import           Input
import qualified Measure as M
import           Sort
import           Utils
import qualified Microbench as MB


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
        (ArrayIn arr) <- getInput bench mb_size
        let fn = sortFn alg parorseq
        putStrLn $ "array size = " ++ show (A.size arr)
        (res0, tmed0, tall0) <- M.benchOnArrays fn arr iters
        unless (isSorted (A.toList res0)) (error $ show bench ++ ": result not sorted.")
        putStrLn "Sorted: OK"
        pure (A.size arr, A.size res0, tmed0, tall0)
      CSort alg -> do
        arr <- getInputAsList alg mb_size
        (res0, tmed0, tall0) <- M.benchAndRunCSorts alg arr iters
        unless (isSorted (res0)) (error $ show bench ++ ": result not sorted.")
        putStrLn "Sorted: OK"
        pure (length arr, length res0, tmed0, tall0)
      CxxSort alg -> do
        arr <- getInputAsList alg mb_size
        (res0, tmed0, tall0) <- M.benchAndRunCxxSorts alg arr iters
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
