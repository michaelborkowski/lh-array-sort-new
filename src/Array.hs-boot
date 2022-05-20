-- We don't have any cyclic module dependencies. This file serves the role of
-- an ML-like signature file for the Array API.

module Array
  (
    -- * Array type
    Array

    -- * Construction and querying
  , make, get, set, slice, size, append, swap

    -- * Linear versions
  , size2, get2

    -- * Convert to/from lists
  , fromList, toList

    -- * LiqidHaskell lemmas
  , lma_gs, lma_gns, lma_swap, lma_swap_eql

  ) where

--------------------------------------------------------------------------------

data Array a

make :: Int -> a -> Array a
get :: Array a -> Int -> a
set :: Array a -> Int -> a -> Array a
slice :: Array a -> Int -> Int -> Array a
size :: Array a -> Int
append :: Array a -> Array a -> Array a
swap :: Array a -> Int -> Int -> Array a
size2 :: Array a -> (Int, Array a)
get2 :: Array a -> Int -> (a, Array a)
fromList :: [a] -> Array a
toList :: Array a -> [a]


--------------------------------------------------------------------------------

lma_gs :: Array a -> Int -> a -> Proof
lma_gns :: Array a -> Int -> Int -> a -> Proof
lma_swap :: Array a -> Int -> Int -> Proof
lma_swap_eql :: Array a -> Int -> Int -> Int -> Proof
