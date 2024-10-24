
{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}

module DpsMerge where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import           Array
import Properties.Equivalence
import Properties.Order

import           Linear.Common
#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
#else
import           Array.List as A
#endif

-- DPS merge
{-@ merge' :: i1:Nat -> i2:Nat
           -> { j:Nat  | i1 + i2 == j }

           -> { xs1:(Array a) | isSorted' xs1 && i1 <= size xs1 }
           -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2 && right xs1 == left xs2 && i2 <= size xs2 }
           -> {  zs:(Array a) | size xs1 + size xs2 == size zs && 

                                j <= size zs &&
                                isSortedBtw zs 0 j &&
                                B.union (toBagBtw xs1 0 i1) (toBagBtw xs2 0 i2) == toBagBtw zs 0 j &&
                                ( j == 0 || i1 == size xs1 || A.get xs1 i1 >= A.get zs (j-1) ) &&
                                ( j == 0 || i2 == size xs2 || A.get xs2 i2 >= A.get zs (j-1) ) }
           
           -> { t:_    | B.union (toBag xs1) (toBag xs2) == toBag (snd t)  &&
                         toSlice zs 0 j == toSlice (snd t) 0 j &&
                         isSorted' (snd t) &&
                         fst t == A.append xs1 xs2 &&
                         token xs1 == token (fst t) &&
                         size (snd t) == size zs && token (snd t) == token zs &&
                         left (snd t) == left zs && right (snd t) == right zs  } / [size zs - j] @-}
merge' :: HasPrimOrd a =>
  Int -> Int -> Int ->
  A.Array a -. A.Array a -. A.Array a -.
  (A.Array a, A.Array a)
merge' i1 i2 j !src1 !src2 !dst =
  let !(Ur len1, src1') = A.size2 src1
      !(Ur len2, src2') = A.size2 src2 in
  if i1 >= len1
  then
    let !(src2'1, dst') = A.copy2 i2 j (len2-i2) src2' dst in (A.append src1' src2'1, dst')
            {- equivalence -}     ? lem_toBagBtw_compose' src1 0 i1 len1
                                  ? lem_toBagBtw_compose' src2 0 i2 len2
                                  ? lem_toBagBtw_compose' dst' 0 j  (A.size dst')
                                  ? lem_equal_slice_bag   dst   dst' 0 (j
                                      ? lem_copy_equal_slice  src2' i2 dst j (len2-i2) )
                                  ? lem_equal_slice_bag'  src2' dst' i2 len2 j (A.size dst')
            {- sortedness -}      ? lem_isSorted_copy src2' i2 dst j (len2-i2)
  else if i2 >= len2
  then
    let !(src1'1, dst') = A.copy2 i1 j (len1-i1) src1' dst in (A.append src1'1 src2', dst')
            {- equivalence -}     ? lem_toBagBtw_compose' src1 0 i1 len1
                                  ? lem_toBagBtw_compose' src2 0 i2 len2
                                  ? lem_toBagBtw_compose' dst' 0 j  (A.size dst')
                                  ? lem_equal_slice_bag   dst   dst' 0 (j
                                      ? lem_copy_equal_slice  src1' i1 dst j (len1-i1) )
                                  ? lem_equal_slice_bag'  src1' dst'  i1 len1 j (A.size dst')
            {- sortedness -}      ? lem_isSorted_copy src1' i1 dst j (len1-i1)
  else
    let !(Ur v1, src1'1) = A.get2 i1 src1'
        !(Ur v2, src2'1) = A.get2 i2 src2' in
    if v1 < v2
    then let dst' = A.setLin j v1 dst
             !(src'', dst'') =  merge' (i1 + 1) i2 (j + 1
                    {- eq -}          ? lem_toBagBtw_right src1 0 (i1+1)
                                      ? lem_bag_union v1 (toBagBtw src1 0 i1) (toBagBtw src2 0 i2)
                                      ? lem_equal_slice_bag    dst dst'   0 (j
                                          ? lem_toSlice_set    dst     j v1)
                                      ? lma_gs dst j v1
                                      ? lem_toBagBtw_right dst' 0 (j+1)
                    {- sor -}         ? lem_isSortedBtw_narrow src1 0 i1 len1 len1
                                      ? lem_equal_slice_sorted dst   dst'  0 0 j j
                                      ? lem_isSortedBtw_build_right  dst'  0 (j
                                            ? if j > 0 then lma_gns dst   j (j-1) v1 else ())
                                 ) src1'1 src2'1 dst' in
         (src'', dst'') ? lem_equal_slice_narrow dst' dst'' 0 0 j (j+1)
    else let dst' = A.setLin j v2 dst
             !(src'', dst'') =  merge' i1 (i2 + 1) (j + 1
                                      ? lem_toBagBtw_right src2 0 (i2+1)
                                      ? lem_bag_union v2 (toBagBtw src1 0 i1) (toBagBtw src2 0 i2)
                                      ? lem_equal_slice_bag    dst dst'   0 (j
                                          ? lem_toSlice_set    dst     j v2)
                                      ? lma_gs dst j v2
                                      ? lem_toBagBtw_right dst' 0 (j+1)
                    {- sor -}         ? lem_isSortedBtw_narrow src2 0 i2 len2 len2
                                      ? lem_equal_slice_sorted dst   dst'  0 0 j j
                                      ? lem_isSortedBtw_build_right  dst'  0 (j
                                            ? if j > 0 then lma_gns dst   j (j-1) v2 else ())
                                 ) src1'1 src2'1 dst' in
         (src'', dst'') ? lem_equal_slice_narrow dst' dst'' 0 0 j (j+1)

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
{-# INLINE merge #-}
{-# SPECIALISE merge :: A.Array Float -. A.Array Float -. A.Array Float -. (A.Array Float, A.Array Float) #-}
{-# SPECIALISE merge :: A.Array Int -. A.Array Int -. A.Array Int -. (A.Array Int, A.Array Int) #-}
merge :: HasPrimOrd a => A.Array a -. A.Array a -. A.Array a -. (A.Array a, A.Array a)
merge src1 src2 dst = merge' 0 0 0 src1 src2 dst   -- the 0's are relative to the current
                                                   --   slices, not absolute indices


--------------------------------------------------------------------------------

{-

goto_seqmerge :: Int
goto_seqmerge = 4

--
-- Version (1): explicitly set the pivot element
--

merge_par :: (HasCallStack, Show a, Ord a) => A.Array a -> A.Array a -> A.Array a -> (A.Array a, A.Array a)
merge_par !src1 !src2 !dst = -- traceShow ("merge_par", A.toList src1, A.toList src2, dst) $
    if A.size dst < goto_seqmerge
    then merge src1 src2 dst
    else let !(n1, src1') = A.size2 src1
             !(n2, src2') = A.size2 src2
             -- !(n3, dst') = A.size2 dst
             dst' = dst
             in if n1 == 0
                then let !(src2'1, dst'') = A.copy2 src2' 0 dst' 0 n2
                     in (A.append src1' src2'1, dst'')
                else if n2 == 0
                     then let !(src1'1, dst'') = A.copy2 src1' 0 dst' 0 n1
                          in (A.append src1'1 src2', dst'')
                     else let mid1 = n1 `div` 2
                              pivot = A.get src1' mid1
                              (mid2, src2'') = binarySearch src2' pivot

                              -- split src1
                              !(src1_l, src1_r) = A.splitAt mid1 src1'
                              !(src1_r1, src1_r2) = A.splitAt 1 src1_r

                              -- split src2
                              !(src2_l, src2_r) = A.splitAt mid2 src2''

                              -- set the pivot
                              !dst1 = A.set dst' (mid1+mid2) pivot

                              -- split dst
                              !(dst_l, dst_r) = A.splitAt (mid1+mid2) dst1
                              !(dst_r1, dst_r2) = A.splitAt 1 dst_r

                              -- sort the sub arrays
                              !(src_l, dst2) = merge_par src1_l src2_l dst_l
                              !(src_r, dst3) = merge_par src1_r2 src2_r dst_r2

                              -- append srcs and dsts
                              src''' = A.append src_l (A.append src1_r1 src_r)
                              dst''' = A.append dst2 (A.append dst_r1 dst3)
                              -- src''' = A.append src_l src_r
                              -- dst''' = A.append dst2 dst3

                          in  -- traceShow (mid1,mid2,pivot,dst1,A.set dst' (mid1+mid2) pivot)
                             -- trace ("pivot=" ++ show pivot) $
                              (src''', dst''')


--
-- Version (2): don't explicit set the pivot
--

merge_par :: (Show a, Ord a) => A.Array a -> A.Array a -> A.Array a -> (A.Array a, A.Array a)
merge_par !src1 !src2 !dst = traceShow ("merge_par", A.toList src1, A.toList src2, dst) $
    if A.size dst < goto_seqmerge
    then merge src1 src2 dst
    else let !(n1, src1') = A.size2 src1
             !(n2, src2') = A.size2 src2
             !(n3, dst')  = A.size2 dst
             in if n1 == 0
                then let !(src2'1, dst'') = A.copy2 src2' 0 dst' 0 n2
                     in (A.append src1' src2'1, dst'')
                else if n2 == 0
                     then let !(src1'1, dst'') = A.copy2 src1' 0 dst' 0 n1
                          in (A.append src1'1 src2', dst'')
                     else let mid1            = n1 `div` 2

                              (pivot, src1'1) = A.get2 src1' mid1
                              (mid2,  src2'1) = binarySearch src2' pivot

                              -- (src1_l, src1'2) = A.slice2 src1'1 0 mid1
                              -- (src1_r, src1'3) = A.slice2 src1'2 mid1 (n1 - mid1 + 1)
                              -- (src2_l, src2'2) = A.slice2 src2'1 0 mid2
                              -- (src2_r, src2'3) = A.slice2 src2'2 mid2 (n2 - mid2 + 1)

                              (src1_l, src1_r) = A.splitAt mid1 src1'1
                              (src2_l, src2_r) = A.splitAt mid2 src2'1

                              -- !dst''           = A.set dst' (mid1+mid2) pivot

                              (dst_l, dst'1)  = A.slice2 dst'  0 (mid1+mid2)
                              (dst_r, dst'2)  = A.slice2 dst'1 (mid1+mid2) (n3 - (mid1+mid2))

                              !(src_l, dst_l') = merge_par src1_l src2_l dst_l
                              !(src_r, dst_r') = merge_par src1_r src2_r dst_r
                              src'''          = A.append src_l  src_r
                              dst'''          = A.append dst_l' dst_r'
                           in trace ("pivot=" ++ show pivot ++ ", mid1=" ++ show mid1 ++ ", mid2=" ++ show mid2
                                     ++ ", arrays=" ++ show (map A.toList [src1_l, src1_r, src2_l, src2_r]) ) $
                                (src''', dst''')

binarySearch :: Ord a => A.Array a -> a -> (Int, A.Array a)
binarySearch ls query = (go 0 (A.size ls), ls)
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

-}
