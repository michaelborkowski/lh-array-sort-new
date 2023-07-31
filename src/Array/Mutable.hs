{-# LANGUAGE CPP              #-}
{-# LANGUAGE MagicHash        #-}
{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE LinearTypes      #-}

-- The Strict pragma is not just for performance, it's necessary for correctness.
-- Without it, this implementation contains a bug related to some thunk/effect
-- remaining unevaluated which causes programs to output wrong answers. Need to
-- debug this some more, but leaving this pragma here for now.
-- {-# LANGUAGE Strict #-}


{-|

Most of the source code here is taken from Data.Array.Mutable.Unlifted.Linear
in [linear-base](https://github.com/tweag/linear-base).

-}
module Array.Mutable where

import qualified Unsafe.Linear as Unsafe
import           Control.DeepSeq ( NFData(..) )
import qualified GHC.Exts as GHC

#ifdef PRIM_MUTABLE_ARRAYS
import           Array.Mutable.PrimUnlifted
import qualified Data.Primitive.Types as P
#else
import           Array.Mutable.Unlifted
#endif

--------------------------------------------------------------------------------
-- Mutable, lifted array API
--------------------------------------------------------------------------------
{-@ data Array a = Array { left :: _, right :: _, arr :: _ } @-}

data Array a = Array { lower :: {-# UNPACK #-} !Int
                     , upper :: {-# UNPACK #-} !Int
                     , array ::                !(Array# a)
                     }


#ifdef PRIM_MUTABLE_ARRAYS
instance (Show a, P.Prim a) => Show (Array a) where
#else
instance Show a => Show (Array a) where
#endif
  show (Array l r arr) =
    "Array { lower = " ++ show l ++ ", upper = " ++ show r ++ ", arr = " ++
    (show $ toList# arr)

instance NFData a => NFData (Array a) where
  rnf (Array lo hi _arr) = rnf lo `seq` rnf hi `seq` ()

{-# INLINE make #-}
make ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Int -> a -> Array a
make 0 _ = Array 0 0 undefined
make s0@(GHC.I# s) x = Array 0 s0 (make# s x)


{-# INLINE makeNoFill #-}

makeNoFill ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Int -> a -> Array a
makeNoFill s0@(GHC.I# s) x =
  Array 0 s0
#ifdef PRIM_MUTABLE_ARRAYS
  (makeNoFill# s x)
#else
  (make# s x)
#endif



{-# INLINE size #-}
size :: Array a -> Int
size (Array !lo !hi _arr) = hi-lo

{-# INLINE get #-}
get ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> Int -> a
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
set ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> Int -> a -> Array a
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

{-# INLINE copy #-}
copy ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> Int -> Array a -> Int -> Int -> Array a
copy s@(Array (GHC.I# lo1) _hi1 src) (GHC.I# src_offset)
      d@(Array (GHC.I# lo2) _hi2 dst) (GHC.I# dst_offset)
      (GHC.I# n) =
#ifdef PRIM_MUTABLE_ARRAYS
  case copy# (get s 0) src (lo1 GHC.+# src_offset) dst (lo2 GHC.+# dst_offset) n of
    dst_arr' -> d { array = dst_arr' }
#else
  case copy# src (lo1 GHC.+# src_offset) dst (lo2 GHC.+# dst_offset) n of
    dst_arr' -> d { array = dst_arr' }
#endif


{-# INLINE copy2 #-}
copy2 ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> Int -> Array a -> Int -> Int -> (Array a, Array a)
copy2 s@(Array (GHC.I# lo1) _hi1 src) (GHC.I# src_offset)
      d@(Array (GHC.I# lo2) _hi2 dst) (GHC.I# dst_offset)
      (GHC.I# n) =
#ifdef PRIM_MUTABLE_ARRAYS
  case copy# (get s 0) src (lo1 GHC.+# src_offset) dst (lo2 GHC.+# dst_offset) n of
    dst_arr' -> (s, d { array = dst_arr' })
#else
  case copy# src (lo1 GHC.+# src_offset) dst (lo2 GHC.+# dst_offset) n of
    dst_arr' -> (s, d { array = dst_arr' })
#endif

{-# INLINE slice #-}
slice :: Array a -> Int -> Int -> Array a
slice (Array l _r !a) l' r' = Array (l+l') (l+r') a

{-# INLINE slice2 #-}
slice2 :: Array a -> Int -> Int -> (Array a, Array a)
slice2 !ar l' r' = (slice ar l' r', ar)

{-# INLINE splitAt #-}
splitAt :: Int -> Array a -> (Array a, Array a)
splitAt m xs = (slice xs 0 m, slice xs m n)
  where
    n = size xs

-- PRE-CONDITION: the two slices are backed by the same array and should be contiguous.
append :: Array a -> Array a -> Array a
append (Array l1 _r1 !a1) (Array _l2 r2 _a2) = Array l1 r2 a1

-- token xs == token ys
-- lem_slice_append :: Array a -> Array a -> ()
-- lem_slice_append xs ys  = ()

size2 :: Array a %1-> (Int, Array a)
size2 = Unsafe.toLinear go
  where
    go !ar = (size ar, ar)

get2 ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> Int -> (a, Array a)
get2 !ar i = (get ar i, ar)

fromList ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  [a] -> Array a
fromList [] = Array 0 0 undefined
fromList ls =
  let a0 = make (length ls) (head ls)
  in foldl (\acc (i,x) -> set acc i x) a0 (zip [0..] ls)

toList ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> [a]
toList arr =
  let ixs = [0..(size arr - 1)]
  in [ get arr i | i <- ixs ]


--------------------------------------------------------------------------------

toList# ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array# a -> [a]
toList# arr =
  let ixs = [0..(GHC.I# (size# arr) - 1)]
  in [ get# arr i | (GHC.I# i) <- ixs ]

fromList# ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  [a] -> Array# a
fromList# [] = make# 0# undefined
fromList# ls =
  let !(GHC.I# len) = length ls
      a0 = make# len (head ls)
  -- in foldl (\acc (i,x) -> set# acc i x) a0 (zip [0..] ls)
  in go a0 (zip [0..] ls)
  where
    -- go :: Array# a -> [(Int,a)] -> Array# a
    go acc []          = acc
    go acc ((GHC.I# i,x):rst) = go (set# acc i x) rst
