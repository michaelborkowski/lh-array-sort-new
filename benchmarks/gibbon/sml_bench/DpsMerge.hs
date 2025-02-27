module DpsMerge where

import Gibbon.Vector

merge' :: (a -> a -> Int) ->
  Vector a -> Vector a -> Vector a ->
  Int -> Int -> Int ->
  (Vector a, Vector a)
merge' cmp src1 src2 dst i1 i2 j =
  let (len1, src1') = size2 src1
      (len2, src2') = size2 src2 in
  if i1 >= len1
  then
    let (src2'1, dst') = copy2 src2' i2 dst j (len2-i2) in (append src1' src2'1, dst')
  else if i2 >= len2
  then
    let (src1'1, dst') = copy2 src1' i1 dst j (len1-i1) in (append src1'1 src2', dst')
  else
    let (v1, src1'1) = get2 src1' i1
        (v2, src2'1) = get2 src2' i2 in
    if cmp v1 v2 < 0
    then let dst' = set dst j v1
             (src'', dst'') =  merge' cmp src1'1 src2'1 dst' (i1 + 1) i2 (j + 1
                                 ) in
         (src'', dst'')
    else let dst' = set dst j v2
             (src'', dst'') =  merge' cmp src1'1 src2'1 dst' i1 (i2 + 1) (j + 1
                                 ) in
         (src'', dst'')

{-# INLINE merge #-}
mergeVerified :: (a -> a -> Int) -> Vector a -> Vector a -> Vector a -> (Vector a, Vector a)
mergeVerified cmp src1 src2 dst = merge' cmp src1 src2 dst 0 0 0
