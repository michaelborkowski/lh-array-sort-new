{-# LANGUAGE BangPatterns #-}

module Microbench where

import qualified Array as A
import           Par

--------------------------------------------------------------------------------

sumArray :: Num a => A.Array a -> a
sumArray arr = go 0 0 (A.size arr)
  where
    go !acc !idx !n =
      if idx == n
      then acc
      else go (acc + A.get arr idx) (idx+1) n

fillArray :: (Int, a) -> A.Array a
fillArray (sz, val) = A.make sz val

seqfib0 :: Int -> Int
seqfib0 n | n < 2 = 1
seqfib0 n =
  let (x,y) = (seqfib0 (n-1), seqfib0 (n-2))
  in (x+y)

parfib0 :: Int -> Int
parfib0 n | n < 10 = seqfib0 n
parfib0 n =
  let (x,y) = tuple2 parfib0 (n-1) parfib0 (n-2)
  in (x+y)
