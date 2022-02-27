{-@ LIQUID "--prune-unsorted" @-}

module DpsMerge where

import qualified Array as A
import Debug.Trace

data Ur a = Ur a

-- Trusted base
get2 :: A.Array a -> Int -> (Ur a, A.Array a)
get2 xs i = (Ur (A.get xs i), xs)

size2 :: A.Array a -> (Ur Int, A.Array a)
size2 xs = (Ur (A.size xs), xs)

-- This is more of a slice join operation than append.
--
-- ASSUMPTION: the two slices are backed by the same array.
--
-- TODO: marge arr1 and arr2 s.t. the result has elements from
--       arr1 for indices l1 to r1 and from arr2 for indices l2 to r2.
append :: A.Array a -> A.Array a -> A.Array a
append (A.Arr arr1 l1 r1) (A.Arr arr2 l2 r2) =
  A.Arr arr1 l1 r2

-- Helper functions
splitMid :: A.Array a -> (A.Array a, A.Array a)
splitMid xs = (A.slice xs 0 m, A.slice xs m n)
  where
    n = A.size xs
    m = n `div` 2

copy :: A.Array a -> A.Array a -> Int -> Int -> (A.Array a, A.Array a)
copy src dst i j =
  let (Ur len, src') = size2 src in
  if i < len
  then
    let (Ur v, src'1) = get2 src' i in
    copy src (A.set dst j v) (i + 1) (j + 1)
  else (src, dst)

-- DPS merge
merge' :: Ord a =>
  A.Array a -> A.Array a -> A.Array a ->
  Int -> Int -> Int ->
  (A.Array a, A.Array a)
merge' src1 src2 dst i1 i2 j =
  let (Ur len1, src1') = size2 src1
      (Ur len2, src2') = size2 src2 in
  if i1 >= len1
  then
    let (src2'1, dst') = copy src2 dst i2 j in
    (append src1' src2'1, dst')
  else if i2 >= len2
  then
    let (src1'1, dst') = copy src1 dst i1 j in
    (append src1'1 src2', dst')
  else
    let (Ur v1, src1'1) = get2 src1' i1
        (Ur v2, src2'1) = get2 src2' i2 in
    if v1 < v2
    then merge' src1'1 src2'1 (A.set dst j v1) (i1 + 1) i2 (j + 1)
    else merge' src1'1 src2'1 (A.set dst j v2) i1 (i2 + 1) (j + 1)

merge :: Ord a => A.Array a -> A.Array a -> A.Array a -> (A.Array a, A.Array a)
merge src1 src2 dst = merge' src1 src2 dst 0 0 0

goto_seqmerge :: Int
goto_seqmerge = 4

merge_par :: (Show a, Ord a) => A.Array a -> A.Array a -> A.Array a -> A.Array a
merge_par src1 src2 dst =
    if A.size dst < goto_seqmerge
    then let (_src', dst') = merge src1 src2 dst
         in dst'
    else let n1 = A.size src1
             n2 = A.size src2
             n3 = A.size dst
             in if n1 == 0
                then let (_src2', dst') = copy src2 dst 0 0
                     in dst'
                else if n2 == 0
                     then let (_src1', dst') = copy src1 dst 0 0
                          in dst'
                     else let mid1 = n1 `div` 2
                              pivot = A.get src1 mid1
                              mid2 = binarySearch src2 pivot
                              src1_l = slice2 0 mid1 src1
                              src1_r = slice2 (mid1+1) (n1 - (mid1+1)) src1
                              src2_l = slice2 0 mid2 src2
                              src2_r = slice2 mid2 (n2-mid2) src2
                              dst1 = A.set dst (mid1+mid2) pivot
                          {-
                              -- Need a true slice of dst; writes to one slice
                              -- should reflect in the other after they're merged.
                              -- The slices backed by lists don't work here since
                              -- each slice is backed by it's own list...
                              --
                              -- Maybe we can make append do this work.
                              dst_l = slice2 0 (mid1+mid2) dst1
                              dst_r = slice2 (mid1+mid2+1) (n3 - (mid1+mid2+1)) dst1
                              dst2 = merge_par src1_l src2_l dst_l
                              dst3 = merge_par src1_r src2_r dst_r
                          -}
                              dst_l = slice2 0 (mid1+mid2) dst1
                              (A.Arr _ lo1 hi1) = slice2 (mid1+mid2+1) (n3 - (mid1+mid2+1)) dst1
                              (A.Arr ls2 lo2 _hi2) = merge_par src1_l src2_l dst_l
                              (A.Arr ls3 _lo3 hi3) = merge_par src1_r src2_r (A.Arr ls2 lo1 hi1)
                          in A.Arr ls3 lo2 hi3
  where
    slice2 :: Int -- starting index
           -> Int -- length of slice
           -> A.Array a
           -> A.Array a
    slice2 i n (A.Arr ls l r) =
        let l' = l + i
            r' = l + i + n
        in if l' > r || r' > r
        then error $ "slice2: out of bound, in=" ++ show (l,r) ++ ", slice=" ++ show (l',r')
        else A.Arr ls l' r'

binarySearch :: Ord a => A.Array a -> a -> Int
binarySearch ls query = go 0 (A.size ls)
  where
    go lo hi = if n == 0
               then lo
               else if query < pivot
                    then go lo mid
                    else go (mid+1) hi
      where
        n = hi - lo
        mid = lo + n `div` 2
        pivot = A.get ls mid

-- DPS mergesort
msortInplace :: (Show a, Ord a) => A.Array a -> A.Array a -> (A.Array a, A.Array a)
msortInplace src tmp =
  let (Ur len, src') = size2 src in
  if len <= 1
  then (src', tmp)
  else
    let (src1, src2) = splitMid src'
        (tmp1, tmp2) = splitMid tmp
        (src1', _tmp1') = msortInplace src1 tmp1
        (src2', _tmp2') = msortInplace src2 tmp2
        tmp3 = append tmp1 tmp2
        (_src'', tmp4) = merge src1' src2' tmp3
    in (tmp4, _src'')

msort :: (Show a, Ord a) => A.Array a -> a -> A.Array a
msort src anyVal =
  let (Ur len, src') = size2 src
      (src'', _tmp) = msortInplace src (A.make len anyVal) in
  _tmp `seq` src''


msort' :: (Show a, Ord a) => A.Array a -> A.Array a
msort' src =
  if A.size src == 0
  then A.Arr [] 0 0
  else msort src (A.get src 0)
