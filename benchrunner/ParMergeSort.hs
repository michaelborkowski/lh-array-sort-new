-- | Fork-join parallel mergesort over unboxed mutable vectors.
--
-- Parallelism strategy:
--   * The recursion tree is forked with 'concurrently_' until the subarray
--     size drops below 'seqThreshold' OR the remaining fork depth reaches 0.
--   * Fork depth starts at @floor(log2(numCapabilities)) + 2@, giving at
--     most @4 * numCapabilities@ live threads — proportional to the number
--     of GHC capabilities set with @+RTS -N#@.
--   * Below the threshold, a sequential introsort ('VI.sort') is used.
--
-- This module is intentionally self-contained so it can serve as a clean
-- baseline without any dependency on the main lh-array-sort library.
module ParMergeSort (sort) where

import           Control.Concurrent.Async     (concurrently_)
import           Data.Bits                    (countLeadingZeros, finiteBitSize)
import           Data.Int                     (Int64)
import           GHC.Conc                     (numCapabilities)
import qualified Data.Vector.Algorithms.Intro as VI
import qualified Data.Vector.Unboxed          as V
import qualified Data.Vector.Unboxed.Mutable  as MV

-- | Minimum subarray length sorted sequentially (matches DpsMergeSort4Par).
seqThreshold :: Int
seqThreshold = 4096

-- | Floor of log base 2, with log2(0) = log2(1) = 0.
intLog2 :: Int -> Int
intLog2 n = max 0 (finiteBitSize n - 1 - countLeadingZeros n)

-- | Sort an unboxed vector of Int64 in parallel.
-- The input vector is not modified; a fresh sorted copy is returned.
sort :: V.Vector Int64 -> IO (V.Vector Int64)
sort vec = do
  mv  <- V.thaw vec
  tmp <- MV.new (MV.length mv)
  let depth = intLog2 (max 1 numCapabilities) + 2
  go depth mv tmp 0 (MV.length mv)
  V.unsafeFreeze mv

-- | Sort mv[lo..hi) in place, using tmp[lo..hi) as scratch space.
go :: Int -> MV.IOVector Int64 -> MV.IOVector Int64 -> Int -> Int -> IO ()
go depth mv tmp lo hi
  | len <= seqThreshold || depth <= 0 = VI.sort (MV.slice lo len mv)
  | otherwise = do
      concurrently_
        (go (depth - 1) mv tmp lo  mid)
        (go (depth - 1) mv tmp mid hi)
      merge mv tmp lo mid hi
  where
    len = hi - lo
    mid = lo + len `div` 2

-- | Merge the already-sorted halves mv[lo..mid) and mv[mid..hi) in place,
-- using tmp[lo..hi) as scratch space.
merge :: MV.IOVector Int64 -> MV.IOVector Int64 -> Int -> Int -> Int -> IO ()
merge mv tmp lo mid hi = do
  -- Copy both halves into scratch space, then merge back.
  MV.copy (MV.slice lo (hi - lo) tmp) (MV.slice lo (hi - lo) mv)
  go' lo mid lo
  where
    go' i j k
      | i >= mid  =   -- left half exhausted; copy remaining right half
          MV.copy (MV.slice k (hi  - j) mv) (MV.slice j (hi  - j) tmp)
      | j >= hi   =   -- right half exhausted; copy remaining left half
          MV.copy (MV.slice k (mid - i) mv) (MV.slice i (mid - i) tmp)
      | otherwise = do
          vi <- MV.unsafeRead tmp i
          vj <- MV.unsafeRead tmp j
          if vi <= vj
            then MV.unsafeWrite mv k vi >> go' (i + 1) j       (k + 1)
            else MV.unsafeWrite mv k vj >> go' i       (j + 1) (k + 1)
