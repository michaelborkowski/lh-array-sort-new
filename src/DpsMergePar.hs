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
--import           DpsMerge

import           Par

#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
#else
import           Array.List as A
#endif

-- DPS merge -- non-parallel, non-consecutive source slices, return them unchanged
             -- unneeded:            fst (fst t) == xs1 && snd (fst t) == xs2 &&
{-@ merge' :: { xs1:(Array a) | isSorted' xs1 }
           -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2 }
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
                         token (fst (fst t)) == token xs1 && token (snd (fst t)) == token xs2 &&
                         left (fst (fst t)) == left xs1 && right (fst (fst t)) == right xs1 &&
                         left (snd (fst t)) == left xs2 && right (snd (fst t)) == right xs2 &&
                         size (snd t) == size zs && token (snd t) == token zs &&
                         left (snd t) == left zs && right (snd t) == right zs  } / [size zs - j] @-} 
merge' :: Ord a =>
  A.Array a -> A.Array a -> A.Array a ->
  Int -> Int -> Int ->
  ((A.Array a, A.Array a), A.Array a)
merge' !src1 !src2 !dst i1 i2 j =
  let !(len1, src1') = A.size2 src1
      !(len2, src2') = A.size2 src2 in
  if i1 >= len1
  then
    let !(src2'1, dst') = A.copy2 src2' i2 dst j (len2-i2) in ((src1', src2'1), dst')
            {- equivalence -}     ? lem_toBagBtw_compose' src1 0 i1 len1
                                  ? lem_toBagBtw_compose' src2 0 i2 len2
                                  ? lem_toBagBtw_compose' dst' 0 j  (A.size dst')
                                  ? lem_equal_slice_bag   dst   dst' 0 (j
                                      ? lem_copy_equal_slice  src2' i2 dst j (len2-i2) )
                                  ? lem_equal_slice_bag'  src2' dst' i2 len2 j (A.size dst')
            {- sortedness -}      ? lem_isSorted_copy src2' i2 dst j (len2-i2)
  else if i2 >= len2
  then
    let !(src1'1, dst') = A.copy2 src1' i1 dst j (len1-i1) in ((src1'1, src2'), dst')
            {- equivalence -}     ? lem_toBagBtw_compose' src1 0 i1 len1
                                  ? lem_toBagBtw_compose' src2 0 i2 len2
                                  ? lem_toBagBtw_compose' dst' 0 j  (A.size dst')
                                  ? lem_equal_slice_bag   dst   dst' 0 (j
                                      ? lem_copy_equal_slice  src1' i1 dst j (len1-i1) )
                                  ? lem_equal_slice_bag'  src1' dst'  i1 len1 j (A.size dst') 
            {- sortedness -}      ? lem_isSorted_copy src1' i1 dst j (len1-i1)
  else
    let !(v1, src1'1) = A.get2 src1' i1
        !(v2, src2'1) = A.get2 src2' i2 in
    if v1 < v2
    then let dst' = A.set dst j v1
             !(src_tup, dst'') =  merge' src1'1 src2'1 dst' (i1 + 1) i2 (j + 1
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
         (src_tup, dst'') ? lem_equal_slice_narrow dst' dst'' 0 0 j (j+1)
    else let dst' = A.set dst j v2
             !(src_tup, dst'') =  merge' src1'1 src2'1 dst' i1 (i2 + 1) (j + 1
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
         (src_tup, dst'') ? lem_equal_slice_narrow dst' dst'' 0 0 j (j+1)

             -- unneeded:            fst (fst t) == xs1 && snd (fst t) == xs2 &&
{-@ merge :: { xs1:(Array a) | isSorted' xs1 }
          -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2  }
          -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
          -> { t:_           | B.union (toBag xs1) (toBag xs2) == toBag (snd t) &&
                               isSorted' (snd t) &&
                               token (fst (fst t)) == token xs1 && token (snd (fst t)) == token xs2 &&
                               token zs  == token (snd t) &&
                               left (fst (fst t)) == left xs1 && right (fst (fst t)) == right xs1 &&
                               left (snd (fst t)) == left xs2 && right (snd (fst t)) == right xs2 &&
                               left (snd t) == left zs  && right (snd t) == right zs  &&
                               size (snd t) == size zs } @-}
{-# INLINE merge #-}
{-# SPECIALISE merge :: A.Array Float -> A.Array Float -> A.Array Float 
                                      -> ((A.Array Float, A.Array Float), A.Array Float) #-}
{-# SPECIALISE merge :: A.Array Int -> A.Array Int -> A.Array Int 
                                    -> ((A.Array Int, A.Array Int), A.Array Int) #-}
merge :: Ord a => A.Array a -> A.Array a -> A.Array a -> ((A.Array a, A.Array a), A.Array a)
merge src1 src2 dst = merge' src1 src2 dst 0 0 0   -- the 0's are relative to the current
                                                   --   slices, not absolute indices




goto_seqmerge :: Int
goto_seqmerge = 4096

{-# INLINE merge_par'' #-}
merge_par'' :: (Show a, Ord a) => (A.Array a, A.Array a, A.Array a) -> ((A.Array a, A.Array a), A.Array a)
merge_par'' (src1, src2, dst) = merge_par' src1 src2 dst

-- unlike in merge, these may not have consecutive slices of the source array
-- unneeded: fst (fst t) == xs1 && snd (fst t) == xs2 &&
{-@ merge_par' :: { xs1:(Array a) | isSorted' xs1 }
               -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2 }
               -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
               -> { t:_           | B.union (toBag xs1) (toBag xs2) == toBag (snd t) &&
                                    token (fst (fst t)) == token xs1 && token (snd (fst t)) == token xs2 &&
                                    token zs  == token (snd t) &&
                                    left (fst (fst t)) == left xs1 && right (fst (fst t)) == right xs1 &&
                                    left (snd (fst t)) == left xs2 && right (snd (fst t)) == right xs2 &&
                                    left (snd t) == left zs  && right (snd t) == right zs  &&
                                    size (snd t) == size zs } / [size xs1] @-} {-
                                    isSorted' (snd t) && -}
merge_par' :: (Show a, Ord a) => A.Array a -> A.Array a -> A.Array a -> ((A.Array a, A.Array a), A.Array a)
merge_par' !src1 !src2 !dst =
  if A.size dst < goto_seqmerge
  then merge src1 src2 dst
  else let !(n1, src1') = A.size2 src1
           !(n2, src2') = A.size2 src2
           !(n3, dst')  = A.size2 dst
        in if n1 == 0
           then let !(src2'1, dst'') = A.copy2 src2' 0 dst' 0 n2
                 in ((src1', src2'1), dst'') ? lem_equal_slice_bag  src2'   dst'' 0 (n2 
                                                   ? lem_copy_equal_slice src2' 0 dst' 0 n2)                                             
           else if n2 == 0
                then let !(src1'1, dst'') = A.copy2 src1' 0 dst' 0 n1  
                      in ((src1'1, src2'), dst'') ? lem_equal_slice_bag  src1'   dst'' 0 (n1 
                                                        ? lem_copy_equal_slice src1' 0 dst' 0 n1)  
                else let mid1            = n1 `div` 2
                         (pivot, src1'1) = A.get2 src1' mid1
                         (mid2,  src2'1) = binarySearch src2' pivot -- src2[mid2] must <= all src1[mid1+1..]
                                                                    --            must >= all src1[0..mid1]
                         (src1_l, src1_cr) = A.splitAt mid1 src1'1
                         (src1_c, src1_r)  = A.splitAt 1    src1_cr
                         (src2_l, src2_r)  = A.splitAt mid2 src2'1

                         (dst_l, dst_cr)   = A.splitAt (mid1+mid2) dst'
                         (dst_c, dst_r)    = A.splitAt 1           dst_cr


                         !dst_c'           = A.set dst_c 0 pivot

                         -- !((src1_l',src2_l'), dst_l')
                         --                   = merge_par' (src1_l ? lem_isSortedBtw_slice src1'1 0  mid1)
                         --                                (src2_l ? lem_isSortedBtw_slice src2'1 0  mid2)
                         --                                dst_l
                         -- !((src1_r',src2_r'), dst_r')
                         --                   = merge_par' (src1_r ? lem_isSortedBtw_slice src1'1 mid1 n1
                         --                                        ? lem_isSortedBtw_slice src1_cr 1 (n1-mid1))
                         --                                (src2_r ? lem_isSortedBtw_slice src2'1 mid2 n2)
                         --                                dst_r

                         (left, right) = tuple2
                                         merge_par''
                                         ( (src1_l ? lem_isSortedBtw_slice src1'1 0  mid1)
                                         , (src2_l ? lem_isSortedBtw_slice src2'1 0  mid2)
                                         , dst_l )
                                         merge_par''
                                         ( (src1_r ? lem_isSortedBtw_slice src1'1 mid1 n1
                                                   ? lem_isSortedBtw_slice src1_cr 1 (n1-mid1))
                                         , (src2_r ? lem_isSortedBtw_slice src2'1 mid2 n2)
                                         , dst_r )
                         (!((src1_l',src2_l'), dst_l'), !((src1_r',src2_r'), dst_r')) = (left, right)

                         src1_cr'     = A.append src1_c  src1_r'
                         src1'3       = A.append src1_l' src1_cr'
                         src2'3       = A.append src2_l' src2_r'
                         dst''        = A.append dst_l' dst_c'
                         dst'''       = A.append dst''  dst_r'
                                      ? lem_toBag_splitAt mid1 src1
                                      ? lem_toBag_splitAt 1    src1_cr
                                      ? lem_toBag_splitAt mid2 src2
                                      ? lem_toBag_append    dst_l' dst_c'
                                      ? lem_toBag_append    dst''  dst_r'
                                      ? lem_equal_slice_bag src1_c dst_c' 0 (1
                                            ? lma_gs dst_c 0 pivot
                                            ? lem_get_slice src1    mid1 n1 mid1
                                            ? lem_get_slice src1_cr 0 1 0
                                            )
                                      -- ? toProof (toBag src1_c === toBag dst_c')
                      in ((src1'3, src2'3), dst''')

{-@ binarySearch :: { ls:_ | isSorted' ls } -> query:_
                         -> { tup:_ | 0 <= fst tup && fst tup <= size ls &&
                                      snd tup == ls &&
                                      ( fst tup == 0 || A.get ls ((fst tup)-1) <= query ) &&
                                      ( fst tup == size ls || query < A.get ls (fst tup) ) } @-}
binarySearch :: Ord a => A.Array a -> a -> (Int, A.Array a) -- must be able to return out of bounds
binarySearch ls query = let (n, ls')  = A.size2 ls
                         in binarySearch' ls' query 0 n

{-@ binarySearch' :: { ls:_ | isSorted' ls } -> query:_  
                          -> { lo:Nat | ( lo == 0       || A.get ls (lo-1) <= query ) } 
                          -> { hi:Nat | ( hi == size ls || query < A.get ls hi ) &&
                                        lo <= hi && hi <= size ls }
                          -> { tup:_ | 0 <= fst tup && fst tup <= size ls && 
                                       snd tup == ls &&
                                       ( fst tup == 0 || A.get ls ((fst tup)-1) <= query ) &&
                                       ( fst tup == size ls || query < A.get ls (fst tup) ) } / [hi-lo] @-}
binarySearch' :: Ord a => A.Array a -> a -> Int -> Int -> (Int, A.Array a)
binarySearch' ls query lo hi = if lo == hi
                               then (lo, ls)
                               else let mid          = lo + (hi - lo) `div` 2
                                        (midElt, ls') = A.get2 ls mid
                                     in if query < midElt
                                        then binarySearch' ls' query lo      mid
                                        else binarySearch' ls' query (mid+1) hi

-- unneeded: fst t == A.append xs1 xs2 &&
{-@ merge_par :: { xs1:(Array a) | isSorted' xs1 }
              -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2 && right xs1 == left xs2 }
              -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
              -> { t:_           | B.union (toBag xs1) (toBag xs2) == toBag (snd t) &&
                                   token (fst t) == token xs1 && 
                                   token zs  == token (snd t) &&
                                   left (fst t) == left xs1 && right (fst t) == right xs2 &&
                                   left (snd t) == left zs  && right (snd t) == right zs  &&
                                   size (snd t) == size zs } / [size xs1] @-} {-
                                   isSorted' (snd t) && -}
{-# INLINE merge_par #-}
{-# SPECIALISE merge_par :: A.Array Float -> A.Array Float -> A.Array Float -> (A.Array Float, A.Array Float) #-}
{-# SPECIALISE merge_par :: A.Array Int -> A.Array Int -> A.Array Int -> (A.Array Int, A.Array Int) #-}
merge_par :: (Show a, Ord a) => A.Array a -> A.Array a -> A.Array a -> (A.Array a, A.Array a)
merge_par !src1 !src2 !dst =
  let !((src1', src2'), dst') = merge_par' src1  src2  dst
      src'                    = A.append   src1' src2'
   in (src', dst')   