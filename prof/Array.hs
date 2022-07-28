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
make s x = Array 0 s (make# s x)

{-# INLINE size #-}
size :: Array a -> Int
size (Array !lo !hi _arr) = hi-lo

{-# INLINE get #-}
get :: Array a -> Int -> a
get (Array lo _hi !arr) i =
  seq
#ifdef RUNTIME_CHECKS
  if i < lo || i > hi
  then (error $ "get: index out of bounds: " ++ show i ++ "," ++ show lo ++ "," ++ show hi)
  else ()
#else
  ()
#endif
  get# arr (lo+i)

{-# INLINE set #-}
set :: Array a -> Int -> a -> Array a
set (Array lo hi !arr) i !a =
  seq
#ifdef RUNTIME_CHECKS
  if i < lo || i > hi
  then (error $ "get: index out of bounds: " ++ show i ++ "," ++ show lo ++ "," ++ show hi)
  else ()
#else
  ()
#endif
  Array lo hi (set# arr (lo+i) a)

{-# INLINE copy2 #-}
copy2 :: Array a -> Int -> Array a -> Int -> Int -> (Array a, Array a)
copy2 s@(Array lo1 _hi1 src) src_offset d@(Array lo2 _hi2 dst) dst_offset n =
  case copy# src (lo1+src_offset) dst (lo2+dst_offset) n of
    dst_arr' -> (s, d { array = dst_arr' })

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

splitMid :: Ord a => Array a -> (Array a, Array a)
splitMid xs = (slice xs 0 m, slice xs m n)
  where
    n = size xs
    m = n `div` 2

swap :: Array a -> Int -> Int -> Array a
swap xs i j = let xi  = get xs i
                  xs' = set xs i (get xs j)
               in set xs' j xi


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
get# (Array# !arr) (GHC.I# i) =
  case GHC.runRW# (GHC.readArray# arr i) of
    (# _, !ret #) -> ret


{-# NOINLINE set# #-}
set# :: Array# a -> Int -> a -> Array# a
set# (Array# !arr) (GHC.I# i) !a =
  case GHC.runRW# (GHC.writeArray# arr i a) of
    _ -> Array# arr

{-# NOINLINE copy# #-}
copy# :: Array# a -> Int -> Array# a -> Int -> Int -> Array# a
copy# (Array# !src) (GHC.I# src_offset) (Array# !dst) (GHC.I# dst_offset) (GHC.I# n) =
  case GHC.runRW# (GHC.copyMutableArray# src src_offset dst dst_offset n) of
    _ -> Array# dst

size# :: Array# a -> Int
size# (Array# arr) =
  let !s = GHC.sizeofMutableArray# arr
  in GHC.I# s

toList# :: Array# a -> [a]
toList# arr =
  let ixs = [0..(size# arr - 1)]
  in [ get# arr i | i <- ixs ]

fromList# :: [a] -> Array# a
fromList# [] = make# 0 undefined
fromList# ls =
  let a0 = make# (length ls) (head ls)
  -- in foldl (\acc (i,x) -> set# acc i x) a0 (zip [0..] ls)
  in go a0 (zip [0..] ls)
  where
    go :: Array# a -> [(Int,a)] -> Array# a
    go acc []          = acc
    go acc ((i,x):rst) = go (set# acc i x) rst
