{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--no-termination"  @-}
{-@ LIQUID "--no-totality"  @-}

{-# LANGUAGE CPP #-}

module DpsMerge4 where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import           Array 
import           Equivalence
import           Order

#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
#else
import           Array.List as A
#endif

-- copy sets dst[j..] <- src[i..]
{-@ copy :: src:(Array a) -> { dst:(Array a) | size dst >= size src }
         -> { i:Nat | i >= 0 && i <= size src && isSorted' src }
         -> { j:Nat | j >= 0 && j <= size dst && (size dst) - j == (size src) - i && 
                      isSortedBtw dst 0 j &&
                      ( i == size src || j == 0 || A.get src i >= A.get dst (j-1) )}
         -> { t:_ | toBagBtw src i (size src) == toBagBtw (snd t) j (size dst) &&
                    toSlice dst 0 j == toSlice (snd t) 0 j &&
                    isSorted' (snd t) &&
                    fst t == src             && token (snd t) == token dst && 
                    left (snd t) == left dst && right (snd t) == right dst &&
                    A.size (snd t) == A.size dst } @-}
copy :: Ord a => A.Array a -> A.Array a -> Int -> Int -> (A.Array a, A.Array a)
copy src dst i j =
  let (len, src') = A.size2 src in
  if i < len
  then
    let (v, src'1)     = A.get2 src' i 
        dst'1          = A.set  dst  j v 
        (src'2, dst'2) = copy src'1 dst'1 (i + 1) (j + 1
             {- sortedness -} ? lma_gs               dst   j v
                              ? lem_isSortedBtw_narrow src 0 i len len 
                              ? lem_toSlice_set        dst         j v 
                              ? lem_equal_slice_sorted dst   dst'1 0 0 j j
--                              ? if j > 0 then A.lma_gns       dst   j (j-1) v else ()
                              ? lem_isSortedBtw_build_right  dst'1 0 (j 
                                   ? if j > 0 then lma_gns       dst   j (j-1) v else ())  
                           ) in
    (src'2, dst'2)     ? toProof ( toBagBtw src i len
            {- equivalence -}  === B.put v (toBagBtw src (i+1) len)
                           --    ? A.lma_gs        dst   j v
                                 ? lem_get_toSlice dst'1 dst'2 0 j (j+1)
                               === B.put (A.get dst'2 j) (toBagBtw dst'2 (j+1) (A.size dst)) 
                               === toBagBtw dst'2 j (A.size dst) )
                   --  ? lem_toSlice_set        dst         j v 
                       ? lem_equal_slice_narrow dst'1 dst'2 0 0 j (j+1) 
  else (src', dst)

-- DPS merge
                              -- left (fst t) == left xs1 && right (fst t) == right xs2 &&
                              -- left (snd t) == left zs  && right (snd t) == right zs  &&
                              -- size (fst t) == size xs1 + size xs2 && size (snd t) == size zs &&
                              -- token xs1 == token (fst t) && token xs2 == token (fst t) && 
{-@ merge' :: { xs1:(Array a) | isSorted' xs1 }
           -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2 && right xs1 == left xs2 }
           -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
           -> { i1:Nat | i1 <= size xs1 } -> { i2:Nat | i2 <= size xs2 }   
           -> { j:Nat  | i1 + i2 == j && j <= size zs && 
                         isSortedBtw zs 0 j &&
                         B.union (toBagBtw xs1 0 i1) (toBagBtw xs2 0 i2) == toBagBtw zs 0 j &&
                         ( j == 0 || i1 == size xs1 || A.get xs1 i1 >= A.get zs (j-1) ) &&
                         ( j == 0 || i2 == size xs2 || A.get xs2 i2 >= A.get zs (j-1) ) }
           -> { t:_    | B.union (toBag xs1) (toBag xs2) == toBag (snd t)  &&
                         toSlice zs 0 j == toSlice (snd t) 0 j &&
                         isSorted' (snd t) &&
                         fst t == A.append xs1 xs2 &&
                         token xs1 == token (fst t) &&
                         token (snd t) == token zs &&
                         left (snd t) == left zs  && right (snd t) == right zs  &&
                         size (snd t) == size zs } @-}
merge' :: Ord a =>
  A.Array a -> A.Array a -> A.Array a ->
  Int -> Int -> Int ->
  (A.Array a, A.Array a)
merge' src1 src2 dst i1 i2 j =
  let (len1, src1') = A.size2 src1
      (len2, src2') = A.size2 src2 in
  if i1 >= len1                 
  then                              
    let (src2'1, dst') = copy src2' dst i2 j in (A.append src1' src2'1, dst')
                       {- equivalence -}      ? lem_toBagBtw_compose' src1 0 i1 len1
                                              ? lem_toBagBtw_compose' src2 0 i2 len2
                                              ? lem_toBagBtw_compose' dst' 0 j  (A.size dst')
                                              ? lem_equal_slice_bag   dst dst' 0 j   
  else if i2 >= len2
  then
    let (src1'1, dst') = copy src1' dst i1 j in (A.append src1'1 src2', dst')
                       {- equivalence -}      ? lem_toBagBtw_compose' src1 0 i1 len1
                                              ? lem_toBagBtw_compose' src2 0 i2 len2
                                              ? lem_toBagBtw_compose' dst' 0 j  (A.size dst')
                                              ? lem_equal_slice_bag   dst dst' 0 j   
  else
    let (v1, src1'1) = A.get2 src1' i1
        (v2, src2'1) = A.get2 src2' i2 in
    if v1 < v2
    then let dst' = A.set dst j v1 
             (src'', dst'') =  merge' src1'1 src2'1 dst' (i1 + 1) i2 (j + 1
                    {- eq -}          ? lem_toBagBtw_right src1 0 (i1+1)
                                      ? lem_bag_union v1 (toBagBtw src1 0 i1) (toBagBtw src2 0 i2)
                                      ? lem_equal_slice_bag    dst dst'   0 (j   
                                          ? lem_toSlice_set    dst     j v1)
                                      ? lma_gs dst j v1
                                      ? lem_toBagBtw_right dst' 0 (j+1)   
                    {- sor -}         ? lem_isSortedBtw_narrow src1 0 i1 len1 len1
                                      -- ? lem_toSlice_set        dst         j v1
                                      ? lem_equal_slice_sorted dst   dst'  0 0 j j
                                      ? lem_isSortedBtw_build_right  dst'  0 (j
                                            ? if j > 0 then lma_gns dst   j (j-1) v1 else ())
                                 ) in
         (src'', dst'') -- ? lem_toSlice_set        dst        j v1
                        ? lem_equal_slice_narrow dst' dst'' 0 0 j (j+1)
    else let dst' = A.set dst j v2 
             (src'', dst'') =  merge' src1'1 src2'1 dst' i1 (i2 + 1) (j + 1
                                      ? lem_toBagBtw_right src2 0 (i2+1)
                                      ? lem_bag_union v2 (toBagBtw src1 0 i1) (toBagBtw src2 0 i2)
                                      ? lem_equal_slice_bag    dst dst'   0 (j   
                                          ? lem_toSlice_set    dst     j v2)
                                      ? lma_gs dst j v2
                                      ? lem_toBagBtw_right dst' 0 (j+1)   
                    {- sor -}         ? lem_isSortedBtw_narrow src2 0 i2 len2 len2
                                      -- ? lem_toSlice_set        dst         j v2
                                      ? lem_equal_slice_sorted dst   dst'  0 0 j j
                                      ? lem_isSortedBtw_build_right  dst'  0 (j
                                            ? if j > 0 then lma_gns dst   j (j-1) v2 else ())
                                 ) in
         (src'', dst'') -- ? lem_toSlice_set        dst        j v2
                        ? lem_equal_slice_narrow dst' dst'' 0 0 j (j+1)

    -- Possible: (right xs1 == left xs2) => (left xs1 == left (fst t) && right xs2 == right (fst t))
{-@ merge :: { xs1:(Array a) | isSorted' xs1 }
          -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2 && right xs1 == left xs2 }
          -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
          -> { t:_           | B.union (toBag xs1) (toBag xs2) == toBag (snd t) &&
                               isSorted' (snd t) &&
                               fst t == A.append xs1 xs2 &&
                               token xs1 == token (fst t) &&
                               token zs  == token (snd t) &&
                               left (snd t) == left zs  && right (snd t) == right zs  &&
                               size (snd t) == size zs } @-}
merge :: Ord a => A.Array a -> A.Array a -> A.Array a -> (A.Array a, A.Array a)
merge src1 src2 dst = merge' src1 src2 dst 0 0 0   -- the 0's are relative to the current
                                                   --   slices, not absolute indices

-- DPS mergesort 
{-
--                      not (token xs == token ys) && right xs == right ys }
{-@ msortSwap :: xs:Array a 
      -> { ys:(Array a ) | A.size ys  == A.size xs   && left xs == left ys && 
                           right xs == right ys }
      -> (Array a, Array a)<{\zs ts -> toBag xs == toBag ts && isSorted' ts &&
                                       token xs == token zs && token ys == token ts &&
                                       A.size xs == A.size zs && A.size ys == A.size ts &&
                                       left zs == left xs && right zs == right xs &&
                                       left ts == left ys && right ts == right ys }> 
       / [A.size xs] @-}
msortSwap :: (Show a, Ord a) => A.Array a -> A.Array a -> (A.Array a, A.Array a)
msortSwap src tmp =
  let (len, src') = A.size2 src in
  if len <= 1
  then let (src'', tmp'') = copy src' tmp 0 0 in
       (src'', tmp'')
  else
    let (src1, src2) = splitMid src'
        (tmp1, tmp2) = splitMid tmp
        (src1', tmp1') = msortInplace src1 tmp1
        (src2', tmp2') = msortInplace src2 tmp2
        tmp3' = A.append tmp1' tmp2' 
        (src'', tmp4) = merge src1' src2' tmp3'
    in (src'', tmp4)  ? lem_toBag_splitMid src -- tmp4 holds the sorted data
                      ? lem_toBag_splitMid tmp   -}

--                      not (token xs == token ys) && right xs == right ys }
{-@ msortInplace :: xs:Array a 
      -> { ys:(Array a ) | A.size ys  == A.size xs   && left xs == left ys && 
                      right xs == right ys }
      -> (Array a, Array a)<{\zs ts -> toBag xs == toBag zs && isSorted' zs &&
                                       token xs == token zs && token ys == token ts &&
                                       A.size xs == A.size zs && A.size ys == A.size ts &&
                                       left zs == left xs && right zs == right xs &&
                                       left ts == left ys && right ts == right ys }> 
       / [A.size xs] @-}
msortInplace :: (Show a, Ord a) => A.Array a -> A.Array a -> (A.Array a, A.Array a)
msortInplace src tmp =
  let (srcA, srcB)   = splitMid src
      (tmpA, tmpB)   = splitMid tmp
      (src1, src2)   = splitMid srcA
      (src3, src4)   = splitMid srcB
      (tmp1, tmp2)   = splitMid tmpA
      (tmp3, tmp4)   = splitMid tmpB
      (src1', tmp1') = msortInplace src1 tmp1
      (src2', tmp2') = msortInplace src2 tmp2
      (src3', tmp3') = msortInplace src3 tmp3
      (src4', tmp4') = msortInplace src4 tmp4
      tmpA'          = A.append tmp1' tmp2'
      tmpB'          = A.append tmp3' tmp4'
      (srcA'', tmpA'') = merge src1' src2' tmpA'
      (srcB'', tmpB'') = merge src3' src4' tmpB'
      src'           = A.append srcA'' srcB''
      (tmp'', src'') = merge tmpA'' tmpB'' src'
  in (src'', tmp'') ? lem_toBag_splitMid src 
                    ? lem_toBag_splitMid tmp
                       ? lem_toBag_splitMid srcA
                       ? lem_toBag_splitMid srcB
                       ? lem_toBag_splitMid tmpA
                       ? lem_toBag_splitMid tmpB
{-
  let (len, src') = A.size2 src in
  if len <= 1
  then (src', tmp)
  else
    let (src1, src2) = splitMid src'
        (tmp1, tmp2) = splitMid tmp
        (src1', tmp1') = msortSwap src1 tmp1
        (src2', tmp2') = msortSwap src2 tmp2
        src3' = A.append src1' src2'  
        (tmp'', src4') = merge tmp1' tmp2' src3' 
    in (src4', tmp'')  ? lem_toBag_splitMid src -- src4' holds the sorted data
                       ? lem_toBag_splitMid tmp   -}

{-@ msort' :: { xs:(Array a) | A.size xs > 0 && left xs == 0 && right xs == size xs }
           -> { y:a | y == A.get xs 0 }
           -> { zs:(Array a) | toBag xs == toBag zs && isSorted' zs &&
                               A.size xs == A.size zs && token xs == token zs } @-}
msort' :: (Show a, Ord a) => A.Array a -> a -> A.Array a
msort' src anyVal =
  let (len, src') = A.size2 src
      (src'', _tmp) = msortInplace src' (A.make len anyVal) in
  _tmp `seq` src''

-- finally, the top-level merge sort function -- TODO: use A.get2/A.size2 for linearity
{-@ msort :: { xs:(A.Array a) | left xs == 0 && right xs == size xs }
                    -> { ys:_ | toBag xs == toBag ys && isSorted' ys &&
                                A.size xs == A.size ys && token xs == token ys  } @-}
msort :: (Show a, Ord a) => A.Array a -> A.Array a
msort src =
  let (len, src') = A.size2 src in
      if len == 0 then src'
      else let (x0, src'') = A.get2 src' 0 in msort' src'' x0


---------------}



{- CODE SECTION NOT IN USE YET

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
                              -- Maybe we can make A.append do this work.
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

END UNUSED SECTION -}

