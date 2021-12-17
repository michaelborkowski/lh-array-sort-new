module DpsMerge where

import Array

data Ur a = Ur a

-- Trusted base
get2 :: Array a -> Int -> (Ur a, Array a)
get2 xs i = (Ur (get xs i), xs)

size2 :: Array a -> (Ur Int, Array a)
size2 xs = (Ur (size xs), xs)

append :: Array a -> Array a -> Array a
append (Arr arr1 l1 r1) (Arr arr2 l2 r2) =
  Arr arr1 l1 r2

-- Helper functions
splitMid :: Array a -> (Array a, Array a)
splitMid xs = (slice xs 0 m, slice xs m n) 
  where 
    n = size xs 
    m = n `div` 2

copy :: Array a -> Array a -> Int -> Int -> (Array a, Array a)
copy src dst i j =
  let (Ur len, src') = size2 src in
  if i < len
  then
    let (Ur v, src'1) = get2 src' i in
    copy src (set dst j v) (i + 1) (j + 1)
  else (src, dst)

-- DPS merge
merge' :: Ord a =>
  Array a -> Array a -> Array a -> 
  Int -> Int -> Int ->
  (Array a, Array a)
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
    then merge' src1'1 src2'1 (set dst j v1) (i1 + 1) i2 (j + 1)
    else merge' src1'1 src2'1 (set dst j v2) i1 (i2 + 1) (j + 1)

merge :: Ord a => Array a -> Array a -> Array a -> (Array a, Array a)
merge src1 src2 dst = merge' src1 src2 dst 0 0 0

-- DPS mergesort
msortInplace :: Ord a => Array a -> Array a -> (Array a, Array a)
msortInplace src tmp =
  let (Ur len, src') = size2 src in
  if len <= 1
  then (src', tmp)
  else
    let (src1, src2) = splitMid src'
        (tmp1, tmp2) = splitMid tmp
        (src1', tmp1') = msortDst src1 tmp1
        (src2', tmp2') = msortDst src2 tmp2
        src'1 = append src1' src2'
        (tmp', src'2) = merge tmp1' tmp2' src'1 in
    (src'2, tmp')

msortDst :: Ord a => Array a -> Array a -> (Array a, Array a)
msortDst src dst =
  let (Ur len, src') = size2 src in
  if len <= 1
  then copy src' dst 0 0
  else
    let (src1, src2) = splitMid src'
        (dst1, dst2) = splitMid dst
        (src1', dst1') = msortInplace src1 dst1
        (src2', dst2') = msortInplace src2 dst2
        dst' = append dst1' dst2' in
    merge src1' src2' dst'

msort :: Ord a => Array a -> a -> Array a
msort src anyVal = 
  let (Ur len, src') = size2 src 
      (src'1, tmp) = msortInplace src (make len anyVal) in
  tmp `seq` src'1
  
