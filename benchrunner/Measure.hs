module Measure where

import Control.Exception (evaluate)
import Control.Monad.Par hiding (runParIO)
import Control.Monad.Par.IO
import Control.DeepSeq
import Data.Int
import System.Mem (performMajorGC)
import Data.Time.Clock (getCurrentTime, diffUTCTime)

import qualified Array as A
import Foreign as F
import Sort
import Utils
import qualified Vector as V
import qualified MVector as MV


benchPar :: (NFData a, NFData b) =>
            (a -> Par b) -> a -> Int -> IO (b, Double, Double)
benchPar f arg iters = do
    let !arg2 = force arg
    let !argsCopied = replicate iters arg2
    tups <- mapM (\arg2' -> dotrialPar f arg2') argsCopied
    let (results, times) = unzip tups
    -- print times
    let  selftimed = median times
         batchtime = sum times
    return $! (last results, selftimed, batchtime)

benchParIO :: (NFData a, NFData b) =>
              (Int -> a -> ParIO b) -> a -> Int -> Int -> IO (b, Double, Double)
benchParIO f arg iters cutoff = do
    let !arg2 = force arg
    tups <- mapM (\_ -> dotrialParIO f arg2 cutoff) [1..iters]
    let (results, times) = unzip tups
    -- print times
    let  selftimed = median times
         batchtime = sum times
    return $! (last results, selftimed, batchtime)

benchIO :: (NFData a, NFData b) =>
              (a -> IO b) -> a -> Int -> IO (b, Double, Double)
benchIO f arg iters = do
    let !arg2 = force arg
    tups <- mapM (\_ -> dotrialIO f arg2) [1..iters]
    let (results, times) = unzip tups
    -- print times
    let  selftimed = median times
         batchtime = sum times
    return $! (last results, selftimed, batchtime)

{-# NOINLINE dotrialPar #-}
dotrialPar :: (NFData a, NFData b) =>
              (a -> Par b) -> a -> IO (b, Double)
dotrialPar f arg = do
    performMajorGC
    t1 <- getCurrentTime
    !a <- evaluate$ runPar $ (f arg)
    t2 <- getCurrentTime
    let delt = fromRational (toRational (diffUTCTime t2 t1))
    putStrLn ("iter time: " ++ show delt)
    return $! (a,delt)

{-# NOINLINE dotrialParIO #-}
dotrialParIO :: (NFData a, NFData b) =>
                (Int -> a -> ParIO b) -> a -> Int -> IO (b, Double)
dotrialParIO f arg cutoff = do
    performMajorGC
    t1 <- getCurrentTime
    !a <- runParIO $ (f cutoff arg)
    t2 <- getCurrentTime
    let delt = fromRational (toRational (diffUTCTime t2 t1))
    putStrLn ("iter time: " ++ show delt)
    return $! (a,delt)

{-# NOINLINE dotrialIO #-}
dotrialIO :: (NFData a, NFData b) =>
                (a -> IO b) -> a -> IO (b, Double)
dotrialIO f arg = do
    performMajorGC
    t1 <- getCurrentTime
    !a <- (f arg)
    t2 <- getCurrentTime
    let delt = fromRational (toRational (diffUTCTime t2 t1))
    putStrLn ("iter time: " ++ show delt)
    return $! (a,delt)

--------------------------------------------------------------------------------

{-# NOINLINE dotrial #-}
dotrial :: (NFData a, Show b, NFData b) => (a %p -> b) -> a -> IO (b, Double)
dotrial f arg = do
    performMajorGC
    t1 <- getCurrentTime
    !a <- evaluate $ (f arg)
    t2 <- getCurrentTime
    let delt = fromRational (toRational (diffUTCTime t2 t1))
    putStrLn ("iter time: " ++ show delt)
    return $! (a,delt)


bench :: (NFData a, Show b, NFData b) => (a %p -> b) -> a -> Int -> IO (b, Double, Double)
bench f arg iters = do
    let !arg2 = force arg
    !tups <- mapM (\_ -> dotrial f arg2) [1..iters]
    let (results, times) = unzip tups
    let selftimed = median times
        batchtime = sum times
    return $! (last results, selftimed, batchtime)

benchOnArrays ::
  (NFData a, Show b, NFData b, Show a, A.HasPrim a) =>
  (A.Array a %p -> b) -> A.Array a -> Int -> IO (b, Double, Double)
benchOnArrays f arr iters = do
  let go (i, a)
        | i == 0 = pure Nothing
        | otherwise = do
            !b <- copyArrayInplaceIO arr a
            res <- dotrial f b
            pure $ Just (res, (i - 1, b))
  !tups <- unfoldrM go (iters, A.make (A.size arr) (A.get arr 0))

  let (results, times) = unzip tups
      selftimed = median times
      batchtime = sum times
  pure (last results, selftimed, batchtime)

benchAndRunDataVecSorts :: VecSort -> Vec -> Int ->  IO (Vec, Double, Double)
benchAndRunDataVecSorts sortfn inVec iters = do
  !tups <- mapM (\_ -> do
                       mvec <- V.thaw inVec
                       mvecCopy <- MV.new (MV.length mvec)
                       MV.copy mvecCopy mvec
                       res <- dotrialLocal sortfn mvecCopy
                       pure res
                ) [1..iters]
  let (results, times) = unzip tups
  -- print times
  let  selftimed = median times
       batchtime = sum times
  return $! (last results, selftimed, batchtime)
  where
    dotrialLocal f arg = do
      performMajorGC
      t1 <- getCurrentTime
      _ <- f arg
      t2 <- getCurrentTime
      let delt = fromRational (toRational (diffUTCTime t2 t1))
      putStrLn ("iter time: " ++ show delt)
      arg' <- V.freeze arg
      return $! (arg', delt)

-- return type : IO ([Int64], Double, Double)
-- [Int64]: sorted output array from the last iteration that was run
-- Double: median runtime from the iterations that were run (selftimed)
-- Double: Total time taken to run all the iterations (batchtime)
benchAndRunCSorts :: SortAlgo -> [Int64] -> Int -> IO ([Int64], Double, Double)
benchAndRunCSorts salg arr iters = do
  !tups <- mapM (\_ -> do
                       !ptr <- newArray arr
                       res <- dotrialC salg (length arr) ptr
                       pure res
                ) [1..iters]
  let (results, times) = unzip tups
  -- print times
  let  selftimed = median times
       batchtime = sum times
  return $! (last results, selftimed, batchtime)
  where
    dotrialC alg arrLength ptr = do
        performMajorGC
        let fn = sortFnC alg
        t1 <- getCurrentTime
        !sortedPtr <- fn ptr (fromIntegral arrLength) (fromIntegral $ F.sizeOf (undefined :: Int64))
        t2 <- getCurrentTime
        let delt = fromRational (toRational (diffUTCTime t2 t1))
        putStrLn ("iter time: " ++ show delt)
        !sortedArr <- peekArray arrLength (castPtr sortedPtr :: Ptr Int64)
        return $! (sortedArr, delt)

-- return type : IO ([Int64], Double, Double)
-- [Int64]: sorted output array from the last iteration that was run
-- Double: median runtime from the iterations that were run (selftimed)
-- Double: Total time taken to run all the iterations (batchtime)
benchAndRunCxxSorts :: SortAlgo -> [Int64] -> Int -> IO ([Int64], Double, Double)
benchAndRunCxxSorts salg arr iters = do
  !tups <- mapM (\_ -> do
                       !ptr <- newArray arr
                       res <- dotrialCxx salg (length arr) ptr
                       pure res
                ) [1..iters]
  let (results, times) = unzip tups
  -- print times
  let  selftimed = median times
       batchtime = sum times
  return $! (last results, selftimed, batchtime)
  where
    dotrialCxx alg arrLength ptr = do
        performMajorGC
        let fn = sortFnCxx alg
        t1 <- getCurrentTime
        !sortedPtr <- fn ptr (fromIntegral arrLength)
        t2 <- getCurrentTime
        let delt = fromRational (toRational (diffUTCTime t2 t1))
        putStrLn ("iter time: " ++ show delt)
        !sortedArr <- peekArray arrLength (castPtr sortedPtr :: Ptr Int64)
        return $! (sortedArr, delt)
