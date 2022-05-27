{-# LANGUAGE CPP              #-}
{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE UnboxedTuples    #-}
{-# LANGUAGE MagicHash        #-}
{-# LANGUAGE BangPatterns     #-}

{-|

Most of the source code here is taken from Data.Array.Mutable.Unlifted.Linear
in [linear-base](https://github.com/tweag/linear-base).

-}
module Array.Mutable {-
  (
    -- * Array type
    Array

    -- * Construction and querying
  , make, get, set, slice, size, append, swap

    -- * Linear versions
  , size2, get2

    -- * Convert to/from lists
  , fromList, toList

  ) -} where

import           Control.DeepSeq ( NFData(..) )
import qualified GHC.Exts as GHC

--------------------------------------------------------------------------------
-- Mutable, lifted array API
--------------------------------------------------------------------------------

data Array a = Array { lower :: {-# UNPACK #-} !Int
                     , upper :: {-# UNPACK #-} !Int
                     , arr   :: Array# a
                     }


instance NFData a => NFData (Array a) where
  rnf x = seq x ()

{-# INLINE make #-}
make :: Int -> a -> Array a
make 0 _ = Array 0 0 undefined
make s x = Array 0 s (make# s x)

{-# INLINE size #-}
size :: Array a -> Int
size (Array _ _ arr) = size# arr

{-# INLINE get #-}
get :: Array a -> Int -> a
get (Array _ _ arr) i =
  seq
#ifdef RUNTIME_CHECKS
  if i < l || i > r
  then (error $ "get: index out of bounds: " ++ show i ++ "," ++ show l ++ "," ++ show r)
  else ()
#else
  ()
#endif
  get# arr i

{-# INLINE set #-}
set :: Array a -> Int -> a -> Array a
set (Array l r arr) i a =
  seq
#ifdef RUNTIME_CHECKS
  if i < l || i > r
  then (error $ "get: index out of bounds: " ++ show i ++ "," ++ show l ++ "," ++ show r)
  else ()
#else
  ()
#endif
  Array l r (set# arr i a)

slice :: Array a -> Int -> Int -> Array a
slice (Array l r a) l' r' = Array (l+l') (l+r') a

-- PRE-CONDITION: the two slices are backed by the same array and should be contiguous.
append :: Array a -> Array a -> Array a
append (Array l1 _r1 a1) (Array _l2 r2 _a2) = Array l1 r2 a1

size2 :: Array a -> (Int, Array a)
size2 ar = (size ar, ar)

get2 :: Array a -> Int -> (a, Array a)
get2 ar i = (get ar i, ar)

fromList :: [a] -> Array a
fromList [] = Array 0 0 undefined
fromList ls =
  let a0 = make (length ls) (head ls)
  in foldl (\acc (i,x) -> set acc i x) a0 (zip [0..] ls)

toList :: Array a -> [a]
toList arr =
  let ixs = [0..(size arr - 1)]
  in [ get arr i | i <- ixs ]


--------------------------------------------------------------------------------
-- Mutable, unlifted array API
--------------------------------------------------------------------------------

-- | A mutable array holding @a@s
newtype Array# a = Array# (GHC.MutableArray# GHC.RealWorld a)

-- The NOINLINE pragmas prevent the runRW# effect from being reordered.

{-# NOINLINE make# #-}
make# :: Int -> a -> Array# a
make# (GHC.I# s) a =
  GHC.runRW# $ \st ->
    case GHC.newArray# s a st of
      (# _, arr #) -> Array# arr


{-# NOINLINE get# #-}
get# :: Array# a -> Int -> a
get# (Array# arr) (GHC.I# i) =
  case GHC.runRW# (GHC.readArray# arr i) of
    (# _, ret #) -> ret


{-# NOINLINE set# #-}
set# :: Array# a -> Int -> a -> Array# a
set# (Array# arr) (GHC.I# i) a =
  case GHC.runRW# (GHC.writeArray# arr i a) of
    _ -> Array# arr

size# :: Array# a -> Int
size# (Array# arr) =
  let !s = GHC.sizeofMutableArray# arr
  in GHC.I# s
