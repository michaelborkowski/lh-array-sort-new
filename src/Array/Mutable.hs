module Array.Mutable
  (
    -- * Array type
    Array

    -- * Construction and querying
  , make, get, set, slice, size, append, swap

    -- * Linear versions
  , size2, get2

    -- * Convert to/from lists
  , fromList, toList

  ) where

--------------------------------------------------------------------------------

data Array a

make :: Int -> a -> Array a
make = _todo

get :: Array a -> Int -> a
get = _todo

set :: Array a -> Int -> a -> Array a
set = _todo

slice :: Array a -> Int -> Int -> Array a
slice = _todo

size :: Array a -> Int
size = _todo

append :: Array a -> Array a -> Array a
append = _todo

swap :: Array a -> Int -> Int -> Array a
swap = _todo

size2 :: Array a -> (Int, Array a)
size2 = _todo

get2 :: Array a -> Int -> (a, Array a)
get2 = _todo

fromList :: [a] -> Array a
fromList = _todo

toList :: Array a -> [a]
toList = _todo
