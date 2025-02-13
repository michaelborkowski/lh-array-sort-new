module Measure ( benchOnArrays, bench, benchPar, benchParIO ) where

import Control.Exception (evaluate)
import Control.Monad.Par hiding (runParIO)
import Control.Monad.Par.IO
import Control.DeepSeq
import Data.Int
import Data.List
import System.Mem (performMajorGC)
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import qualified Array as A

--------------------------------------------------------------------------------

median :: [Double] -> Double
median ls = (sort ls) !! (length ls `div` 2)

--------------------------------------------------------------------------------


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

bench :: (NFData a, Show b, NFData b) => (a -> b) -> a -> Int -> IO (b, Double, Double)
bench f arg iters = do
    let !arg2 = force arg
    !tups <- mapM (\_ -> dotrial f arg2) [1..iters]
    let (results, times) = unzip tups
    let selftimed = median times
        batchtime = sum times
    return $! (last results, selftimed, batchtime)

benchOnArrays :: (NFData a, Show b, NFData b, Show a) => (A.Array a -> b) -> [A.Array a] -> Int -> IO (b, Double, Double)
benchOnArrays f arrArgs iters = do 
    let !arg2s = force arrArgs
    !tups <- mapM (\arg2' -> dotrial f (force arg2')) arg2s
    let (results, times) = unzip tups
    let selftimed = median times
        batchtime = sum times
    return $! (last results, selftimed, batchtime)

{-# NOINLINE dotrial #-}
dotrial :: (NFData a, Show b, NFData b) => (a -> b) -> a -> IO (b, Double)
dotrial f arg = do
    performMajorGC
    t1 <- getCurrentTime
    !a <- evaluate $ (f arg)
    t2 <- getCurrentTime
    let delt = fromRational (toRational (diffUTCTime t2 t1))
    putStrLn ("iter time: " ++ show delt)
    return $! (a,delt)
