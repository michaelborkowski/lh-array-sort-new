{-# LANGUAGE BangPatterns #-}

module Sort where

import qualified Array as A

import           Prelude
import qualified Data.Vector.Unboxed as V

--------------------------------------------------------------------------------

-- DPS mergesort
msortSwap :: (Show a, Ord a) => A.Array a -> A.Array a -> (A.Array a, A.Array a)
msortSwap src tmp =
  let (len, src') = A.size2 src in
  if len == 1
  -- then let (src'', tmp'') = copy src' tmp 0 0 in
  then let (src'', tmp'') = A.copy2 src' 0 tmp 0 1 in
       (src'', tmp'')
  else
    let (src1, src2) = A.splitMid src'
        (tmp1, tmp2) = A.splitMid tmp
        (src1', tmp1') = msortInplace src1 tmp1
        (src2', tmp2') = msortInplace src2 tmp2
        tmp3' = A.append tmp1' tmp2'
        (src'', tmp4) = merge src1' src2' tmp3'
    in (src'', tmp4)

msortInplace :: (Show a, Ord a) => A.Array a -> A.Array a -> (A.Array a, A.Array a)
msortInplace src tmp =
  let (len, src') = A.size2 src in
  if len <= 1
  then (src', tmp)
  else
    let (src1, src2) = A.splitMid src'
        (tmp1, tmp2) = A.splitMid tmp
        (src1', tmp1') = msortSwap src1 tmp1
        (src2', tmp2') = msortSwap src2 tmp2
        src3' = A.append src1' src2'
        (tmp'', src4') = merge tmp1' tmp2' src3'
    in (src4', tmp'')

msort' :: (Show a, Ord a) => A.Array a -> a -> A.Array a
msort' src anyVal =
  let (len, src') = A.size2 src
      (src'', _tmp) = msortInplace src' (A.make len anyVal) in
  _tmp `seq` src''

-- finally, the top-level merge sort function
{-# SPECIALISE msort :: A.Array Float -> A.Array Float #-}
{-# SPECIALISE msort :: A.Array Int -> A.Array Int #-}
msort :: (Show a, Ord a) => A.Array a -> A.Array a
msort src =
  let (len, src') = A.size2 src in
      if len == 0 then src'
      else let (x0, src'') = A.get2 src' 0 in msort' src'' x0


--------------------------------------------------------------------------------

{-

-- copy sets dst[j..] <- src[i..]
copy :: Ord a => A.Array a -> A.Array a -> Int -> Int -> (A.Array a, A.Array a)
copy src dst i j =
  let (len, src') = A.size2 src in
  if i < len
  then
    let (v, src'1)     = A.get2 src' i
        dst'1          = A.set  dst  j v
        (src'2, dst'2) = copy src'1 dst'1 (i + 1) (j + 1) in
    (src'2, dst'2)
  else (src', dst)

-}

-- DPS merge
merge' :: Ord a =>
  A.Array a -> A.Array a -> A.Array a ->
  Int -> Int -> Int ->
  (A.Array a, A.Array a)
merge' src1 src2 dst i1 i2 j =
  let (len1, src1') = A.size2 src1
      (len2, src2') = A.size2 src2 in
  if i1 >= len1
  then
    -- let (src2'1, dst') = copy src2' dst i2 j in (A.append src1' src2'1, dst')
    let (src2'1, dst') = A.copy2 src2' i2 dst j (len2-i2+1) in (A.append src1' src2'1, dst')
  else if i2 >= len2
  then
    -- let (src1'1, dst') = copy src1' dst i1 j in (A.append src1'1 src2', dst')
    let (src1'1, dst') = A.copy2 src1' i1 dst j (len1-i1+1) in (A.append src1'1 src2', dst')
  else
    let (v1, src1'1) = A.get2 src1' i1
        (v2, src2'1) = A.get2 src2' i2 in
    if v1 < v2
    then let dst' = A.set dst j v1
             (src'', dst'') =  merge' src1'1 src2'1 dst' (i1 + 1) i2 (j + 1) in
         (src'', dst'')
    else let dst' = A.set dst j v2
             (src'', dst'') =  merge' src1'1 src2'1 dst' i1 (i2 + 1) (j + 1) in
         (src'', dst'')

{-# INLINE merge #-}
merge :: Ord a => A.Array a -> A.Array a -> A.Array a -> (A.Array a, A.Array a)
merge src1 src2 dst = merge' src1 src2 dst 0 0 0   -- the 0's are relative to the current
                                                   --   slices, not absolute indices
