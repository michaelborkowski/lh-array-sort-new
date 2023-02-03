-- We don't have any cyclic module dependencies. This file serves the role of
-- an ML-like signature file for the Array API.

module Array
  (
    -- * Array type
    Array

    -- * Construction and querying
  , alloc, make, size, get, set, slice, append, splitMid, swap

    -- * Linear versions
  , size2, get2, slice2, copy2

    -- * Convert to/from lists
  , fromList, toList

    -- * Parallel tuple operator
  , (.||.)

    -- * LiqidHaskell lemmas
  , lma_gs, lma_gns, lma_swap, lma_swap_eql, lem_slice_append, lem_get_slice

  ) where

--------------------------------------------------------------------------------

data Array a

alloc :: Int -> a -> (Array a %1-> Ur b) -> Ur b
make :: Int -> a -> Array a
size :: Array a -> Int
get :: Array a -> Int -> a
set :: Array a -> Int -> a -> Array a
slice :: Array a -> Int -> Int -> Array a
append :: Array a -> Array a -> Array a
splitMid :: Array a %1-> (Array a, Array a)
swap :: Array a %1-> Int -> Int -> Array a
size2 :: Array a %1-> (Int, Array a)
get2 :: Array a -> Int -> (a, Array a)
slice2 :: Array a -> Int -> Int -> (Array a, Array a)
copy2 :: Array a -> Int -> Array a -> Int -> Int -> (Array a, Array a)
fromList :: [a] -> Array a
toList :: Array a -> [a]

-- TODO:
size2 :: Array a %1-> (Ur Int, Array a)
get2 :: Array a %1-> Int -> (Ur a, Array a)


-- This doesn't belong here, but it's here for convenience.
-- Parallel tuple combinator.
(.||.) :: a -> b -> (a,b)

--------------------------------------------------------------------------------

lma_gs :: Array a -> Int -> a -> Proof
lma_gns :: Array a -> Int -> Int -> a -> Proof
lma_swap :: Array a -> Int -> Int -> Proof
lma_swap_eql :: Array a -> Int -> Int -> Int -> Proof
lem_slice_append :: Array a -> Array a -> Proof
lem_get_slice :: Array a -> Int -> Int -> Int -> Proof
