module DpsMergeSort where

import Gibbon.Vector

-- DPS mergesort
msortSwap :: (a -> a -> Int) -> Vector a -> Vector a -> (Vector a, Vector a)
msortSwap cmp src tmp =
  let (len, src') = size2 src in
  if len <= 1
  then let (src'', tmp'') = copy2 src' 0 tmp 0 len in
       (src'', tmp'')
  else
    let (src1, src2) = splitMid src'
        (tmp1, tmp2) = splitMid tmp
        (src1', tmp1') = msortInplace cmp src1 tmp1
        (src2', tmp2') = msortInplace cmp src2 tmp2
        tmp3' = append tmp1' tmp2'
        (src'', tmp4) = mergeVerified cmp src1' src2' tmp3'
    in (src'', tmp4)

msortInplace :: (a -> a -> Int) -> Vector a -> Vector a -> (Vector a, Vector a)
msortInplace cmp src tmp =
  let (len, src') = size2 src in
  if len <= 1
  then (src', tmp)
  else
    let (src1, src2) = splitMid src'
        (tmp1, tmp2) = splitMid tmp
        (src1', tmp1') = msortSwap cmp src1 tmp1
        (src2', tmp2') = msortSwap cmp src2 tmp2
        src3' = append src1' src2'
        (tmp'', src4') = mergeVerified cmp tmp1' tmp2' src3'
    in (src4', tmp'')

msort' :: (a -> a -> Int) -> Vector a -> a -> Vector a
msort' cmp src anyVal =
  let (len, src1) = size2 src
      (a, _) = msortInplace cmp src1 (copy src1)
      src2 = copy a in
  src2

msort :: (a -> a -> Int) -> Vector a -> Vector a
msort cmp src =
  let (len, src1) = size2 src in
      if len == 0 then src1
      else let (x0, src2) = get2 src1 0
               cpy2 = copy src2
           in msort' cmp cpy2 x0
