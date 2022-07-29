{-# LANGUAGE CPP              #-}
{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE UnboxedTuples    #-}
{-# LANGUAGE MagicHash        #-}
{-# LANGUAGE BangPatterns     #-}

-- The Strict pragma is not just for performance, it's necessary for correctness.
-- Without it, this implementation contains a bug related to some thunk/effect
-- remaining unevaluated which causes programs to output wrong answers. Need to
-- debug this some more, but leaving this pragma here for now.
-- {-# LANGUAGE Strict #-}


{-|

Most of the source code here is taken from Data.Array.Mutable.Unlifted.Linear
in [linear-base](https://github.com/tweag/linear-base).

-}
module Array where

import           Control.DeepSeq ( NFData(..) )
import qualified GHC.Exts as GHC

--------------------------------------------------------------------------------
-- Mutable, lifted array API
--------------------------------------------------------------------------------

data Array a = Array { lower :: {-# UNPACK #-} !Int
                     , upper :: {-# UNPACK #-} !Int
                     , array :: {-# UNPACK #-} !(Array# a)
                     }

instance Show a => Show (Array a) where
  show (Array l r arr) =
    "Array { lower = " ++ show l ++ ", upper = " ++ show r ++ ", arr = " ++
    (show $ toList# arr)

instance NFData a => NFData (Array a) where
  rnf (Array lo hi _arr) = rnf lo `seq` rnf hi `seq` ()

{-# INLINE make #-}
make :: Int -> a -> Array a
make 0 _ = Array 0 0 undefined
make (GHC.I# s) x = Array 0 (GHC.I# s) (make# s x)

{-# INLINE size #-}
size :: Array a -> Int
size (Array !lo !hi _arr) = hi-lo

{-# INLINE get #-}
get :: Array a -> Int -> a
get (Array (GHC.I# lo) _hi !arr) (GHC.I# i) =
  seq
#ifdef RUNTIME_CHECKS
  if i < lo || i > hi
  then (error $ "get: index out of bounds: " ++ show i ++ "," ++ show lo ++ "," ++ show hi)
  else ()
#else
  ()
#endif
  get# arr (lo GHC.+# i)

{-# INLINE set #-}
set :: Array a -> Int -> a -> Array a
set (Array (GHC.I# lo) hi !arr) (GHC.I# i) !a =
  seq
#ifdef RUNTIME_CHECKS
  if i < lo || i > hi
  then (error $ "get: index out of bounds: " ++ show i ++ "," ++ show lo ++ "," ++ show hi)
  else ()
#else
  ()
#endif
  Array (GHC.I# lo) hi (set# arr (lo GHC.+# i) a)

{-# INLINE copy2 #-}
copy2 :: Array a -> Int -> Array a -> Int -> Int -> (Array a, Array a)
copy2 s@(Array (GHC.I# lo1) _hi1 src) (GHC.I# src_offset)
      d@(Array (GHC.I# lo2) _hi2 dst) (GHC.I# dst_offset)
      (GHC.I# n)
  = case copy# src (lo1 GHC.+# src_offset) dst (lo2 GHC.+# dst_offset) n of
      dst_arr' -> (s, d { array = dst_arr' })

{-# INLINE slice #-}
slice :: Array a -> Int -> Int -> Array a
slice (Array l _r !a) l' r' = Array (l+l') (l+r') a

-- PRE-CONDITION: the two slices are backed by the same array and should be contiguous.
append :: Array a -> Array a -> Array a
append (Array l1 _r1 !a1) (Array _l2 r2 _a2) = Array l1 r2 a1

size2 :: Array a -> (Int, Array a)
size2 !ar = (size ar, ar)

get2 :: Array a -> Int -> (a, Array a)
get2 !ar i = (get ar i, ar)

fromList :: [a] -> Array a
fromList [] = Array 0 0 undefined
fromList ls =
  let a0 = make (length ls) (head ls)
  in foldl (\acc (i,x) -> set acc i x) a0 (zip [0..] ls)

toList :: Array a -> [a]
toList arr =
  let ixs = [0..(size arr - 1)]
  in [ get arr i | i <- ixs ]

{-# INLINE splitMid #-}
splitMid :: Ord a => Array a -> (Array a, Array a)
splitMid xs = (slice xs 0 m, slice xs m n)
  where
    n = size xs
    m = n `div` 2

{-# INLINE swap #-}
swap :: Array a -> Int -> Int -> Array a
swap xs i j =
  let xi  = get xs i
      xs' = set xs i (get xs j)
      xs'' = set xs' j xi
  in xs''


--------------------------------------------------------------------------------
-- Mutable, unlifted array API
--------------------------------------------------------------------------------

-- | A mutable array holding @a@s
newtype Array# a = Array# (GHC.MutableArray# GHC.RealWorld a)

-- The NOINLINE pragmas prevent the runRW# effect from being reordered.

{-# NOINLINE make# #-}
make# :: GHC.Int# -> a -> Array# a
make# s a =
  GHC.runRW# $ \st ->
    case GHC.newArray# s a st of
      (# _, arr #) -> Array# arr


{-# NOINLINE get# #-}
get# :: Array# a -> GHC.Int# -> a
get# (Array# !arr) i =
  case GHC.runRW# (GHC.readArray# arr i) of
    (# _, !ret #) -> ret


{-# NOINLINE set# #-}
set# :: Array# a -> GHC.Int# -> a -> Array# a
set# (Array# !arr) i !a =
  case GHC.runRW# (GHC.writeArray# arr i a) of
    _ -> Array# arr

{-# NOINLINE copy# #-}
copy# :: Array# a -> GHC.Int# -> Array# a -> GHC.Int# -> GHC.Int# -> Array# a
copy# (Array# !src) src_offset (Array# !dst) dst_offset n =
  case GHC.runRW# (GHC.copyMutableArray# src src_offset dst dst_offset n) of
    _ -> Array# dst

size# :: Array# a -> Int
size# (Array# arr) =
  let !s = GHC.sizeofMutableArray# arr
  in GHC.I# s

toList# :: Array# a -> [a]
toList# arr =
  let ixs = [0..(size# arr - 1)]
  in [ get# arr i | (GHC.I# i) <- ixs ]

fromList# :: [a] -> Array# a
fromList# [] = make# 0# undefined
fromList# ls =
  let (GHC.I# len)= (length ls)
      a0 = make# len (head ls)
  -- in foldl (\acc (i,x) -> set# acc i x) a0 (zip [0..] ls)
  in go a0 (zip [0..] ls)
  where
    go :: Array# a -> [(Int,a)] -> Array# a
    go acc []          = acc
    go acc ((GHC.I# i,x):rst) = go (set# acc i x) rst
