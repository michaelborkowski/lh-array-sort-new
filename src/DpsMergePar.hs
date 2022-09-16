{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection"  @-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}

module DpsMergePar where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import           Array 
import           Equivalence
import           Order
import           DpsMerge

#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
#else
import           Array.List as A
#endif

-- DPS merge
{- @ merge' :: { xs1:(Array a) | isSorted' xs1 }
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
                         size (snd t) == size zs } / [size zs - j] @- }
    let (src2'1, dst') = copy src2' dst i2 j in (A.append src1' src2'1, dst')
                       {- equivalence -}      ? lem_toBagBtw_compose' src1 0 i1 len1
                                              ? lem_toBagBtw_compose' src2 0 i2 len2
                                              ? lem_toBagBtw_compose' dst' 0 j  (A.size dst')
                                              ? lem_equal_slice_bag   dst dst' 0 j   
    let (src1'1, dst') = copy src1' dst i1 j in (A.append src1'1 src2', dst')
                       {- equivalence -}      ? lem_toBagBtw_compose' src1 0 i1 len1
                                              ? lem_toBagBtw_compose' src2 0 i2 len2
                                              ? lem_toBagBtw_compose' dst' 0 j  (A.size dst')
                                              ? lem_equal_slice_bag   dst dst' 0 j   
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
                                      ? lem_equal_slice_sorted dst   dst'  0 0 j j
                                      ? lem_isSortedBtw_build_right  dst'  0 (j
                                            ? if j > 0 then lma_gns dst   j (j-1) v1 else ())
                                 ) in
         (src'', dst'') ? lem_equal_slice_narrow dst' dst'' 0 0 j (j+1)
    else let dst' = A.set dst j v2 
             (src'', dst'') =  merge' src1'1 src2'1 dst' i1 (i2 + 1) (j + 1
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
                                 ) in
         (src'', dst'') ? lem_equal_slice_narrow dst' dst'' 0 0 j (j+1)
-}

goto_seqmerge :: Int
goto_seqmerge = 4

{-@ merge_par :: { xs1:(Array a) | isSorted' xs1 }
              -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2 && right xs1 == left xs2 }
              -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
              -> { t:_           | B.union (toBag xs1) (toBag xs2) == toBag (snd t) &&
                                   isSorted' (snd t) &&
                                   fst t == A.append xs1 xs2 &&
                                   token xs1 == token (fst t) &&
                                   token zs  == token (snd t) &&
                                   left (snd t) == left zs  && right (snd t) == right zs  &&
                                   size (snd t) == size zs } @-}
merge_par :: (Show a, Ord a) => A.Array a -> A.Array a -> A.Array a -> (A.Array a, A.Array a)
merge_par !src1 !src2 !dst =
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

                              (src1_l, src1'2) = slice2 src1'1 0 mid1 
                              (src1_r, src1'3) = slice2 src1'2 mid1 (n1 - mid1) 
                              (src2_l, src2'2) = slice2 src2'1 0 mid2 
                              (src2_r, src2'3) = slice2 src2'2 mid2 (n2 - mid2) 
--                              !dst''           = A.set dst' (mid1+mid2) pivot
                              (dst_l, dst'1)  = slice2 dst'  0 (mid1+mid2) 
                              (dst_r, dst'2)  = slice2 dst'1 (mid1+mid2) (n3 - (mid1+mid2))

                              !(src_l, dst_l') = merge_par src1_l src2_l dst_l
                              !(src_r, dst_r') = merge_par src1_r src2_r dst_r
                              src'''          = A.append src_l  src_r
                              dst''           = A.append dst_l' dst_r'  
                           in (src''', dst'')

{-@ binarySearch :: ls_: -> q:_ 
                         -> { tup:_ | 0 <= fst tup && fst tup < size ls && 
                                      snd tup == ls &&
                                      ( fst tup == size ls || query < A.get ls (fst tup) ) } @-}
binarySearch :: Ord a => A.Array a -> a -> (Int, A.Array a)
binarySearch ls query = let (n, ls')  = A.size2 ls
                         in binarySearch' ls' query 0 n

{-@ binarySearch' :: ls_: -> q:_ -> lo:Nat -> { hi:_ | lo <= hi && hi <= size ls }
                          -> { tup:_ | 0 <= fst tup && fst tup < size ls && 
                                       snd tup == ls &&
                                       ( fst tup == size ls || query < A.get ls (fst tup) ) } @-}
binarySearch' :: Ord a => A.Array a -> a -> Int -> Int -> (Int, A.Array a)
binarySearch' ls query lo hi = if lo == hi
                               then (lo, ls)
                               else let mid          = lo + (hi - lo) `div` 2
                                        (pivot, ls') = A.get2 ls mid
                                     in if query < pivot
                                        then binarySearch' ls' query lo      mid
                                        else binarySearch' ls' query (mid+1) hi
