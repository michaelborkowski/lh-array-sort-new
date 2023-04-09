{-# LANGUAGE BangPatterns #-}

module Microbench where

import           GHC.Conc ( par, pseq )
import           Data.Int ( Int64 )
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

{-# NOINLINE seqfib #-}
seqfib :: Int64 -> Int64
seqfib !n | n < 2 = 1
seqfib !n = seqfib (n-1) + seqfib (n-2)

parfib :: Int64 -> Int64
parfib !n | n < 33 = seqfib n
parfib !n =
  x `par` y `pseq` (x+y)
  where
    x = parfib (n-1)
    y = parfib (n-2)
