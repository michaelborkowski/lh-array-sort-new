{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE UnboxedTuples    #-}
{-# LANGUAGE MagicHash        #-}

{-|

Most of the source code here is taken from Data.Array.Mutable.Unlifted.Linear
in [linear-base](https://github.com/tweag/linear-base).

-}
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

import           Control.DeepSeq ( NFData(..) )
import qualified GHC.Exts as GHC

--------------------------------------------------------------------------------
-- Mutable, lifted array API
--------------------------------------------------------------------------------

data Array a = Array (Array# a)

instance NFData a => NFData (Array a) where
  rnf x = seq x ()

{-# INLINE make #-}
make :: Int -> a -> Array a
make s x = Array (make# s x)

{-# INLINE get #-}
get :: Array a -> Int -> a
get (Array arr) i = get# arr i

{-# INLINE set #-}
set :: Array a -> Int -> a -> Array a
set (Array arr) i a = Array (set# arr i a)

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


--------------------------------------------------------------------------------
-- Mutable, unlifted array API
--------------------------------------------------------------------------------

-- | A mutable array holding @a@s
newtype Array# a = Array# (GHC.MutableArray# GHC.RealWorld a)

{-# NOINLINE make# #-} -- prevents runRW# effect from being reordered
make# :: Int -> a -> Array# a
make# (GHC.I# s) a =
  GHC.runRW# $ \st ->
    case GHC.newArray# s a st of
      (# _, arr #) -> Array# arr


{-# NOINLINE get# #-} -- prevents the runRW# effect from being reordered
get# :: Array# a -> Int -> a
get# (Array# arr) (GHC.I# i) =
  case GHC.runRW# (GHC.readArray# arr i) of
    (# _, ret #) -> ret


{-# NOINLINE set# #-} -- prevents the runRW# effect from being reordered
set# :: Array# a -> Int -> a -> Array# a
set# (Array# arr) (GHC.I# i) a =
  case GHC.runRW# (GHC.writeArray# arr i a) of
    _ -> Array# arr
