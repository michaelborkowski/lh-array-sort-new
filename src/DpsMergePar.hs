{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--short-names" @-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}

module DpsMergePar where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import           Array
import           Equivalence
import           Order
import           DpsMergeParSeqFallback

import           Par

#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
#else
import           Array.List as A
#endif
import qualified Array as A

--------------------------------------------------------------------------------
-- | Parallel Merge -- Proofs for Sortedness and Equivalence
--------------------------------------------------------------------------------

{-@ reflect goto_seqmerge @-}
goto_seqmerge :: Int
goto_seqmerge = 4096

--      -> { i1:Nat | i1 <= size xs1 } -> { i2:Nat | i2 <= size xs2 }
--      -> { j:Nat  | i1 + i2 == j && j <= size zs }
 
-- unlike in merge, these may not have consecutive slices of the source array
-- input tuple is ((xs1, xs2), zs)    -- TODO: condense the post-conditions

-- save sorted and equiv for the lemmas -- only output the destination
{-@ reflect merge_par_func @-}
{-@ merge_par_func :: xs1:(Array a) -> { xs2:(Array a) | token xs1 == token xs2 }
      -> { zs :(Array a) | size xs1 + size xs2 == size zs }
      -> { zs':_  | size zs' == size zs && token zs' == token zs &&
                    left zs' == left zs && right zs' == right zs  } / [size xs1] @-} 
merge_par_func :: HasPrimOrd a => A.Array a -> A.Array a -> A.Array a -> A.Array a 
merge_par_func src1 src2 dst {-!((src1, src2), dst)-} =
    if A.size dst < goto_seqmerge
    then merge_func src1 src2 dst 0 0 0 -- merge src1 src2 dst
    else if n1 == 0
         then A.copy src2 0 dst 0 n2 {-
                let !(src2'1, dst'') = A.copy2_par src2' 0 dst' 0 n2
                 in ((src1', src2'1), dst'') -}  {-? lem_equal_slice_bag  src2'   dst'' 0 (n2
                                                   ? lem_copy_equal_slice src2' 0 dst' 0 n2)-}
         else if n2 == 0
              then A.copy src1 0 dst 0 n1 {-
                    let !(src1'1, dst'') = A.copy2_par src1' 0 dst' 0 n1
                      in ((src1'1, src2'), dst'')-} {-? lem_equal_slice_bag  src1'   dst'' 0 (n1
                                                        ? lem_copy_equal_slice src1' 0 dst' 0 n1)-}
              else let mid1  = n1 `div` 2
                       pivot = A.get src1 mid1
                       mid2  = binarySearch_func src2 pivot -- src2[mid2] must <= all src1[mid1+1..]
                                                            --            must >= all src1[0..mid1]
                       (src1_l, src1_cr) = A.splitAt mid1 src1
                       (src1_c, src1_r)  = A.splitAt 1    src1_cr
                       (src2_l, src2_r)  = A.splitAt mid2 src2

                       (dst_l, dst_cr)   = A.splitAt (mid1+mid2) dst
                       (dst_c, dst_r)    = A.splitAt 1           dst_cr

                       dst_l'            = merge_par_func (src1_l {-? lem_isSortedBtw_slice src1 0 mid1-})
                                                          (src2_l {-? lem_isSortedBtw_slice src2 0 mid2-})
                                                          dst_l
                       dst_c'            = A.set dst_c 0 pivot
                       dst_r'            = merge_par_func (src1_r {-? lem_isSortedBtw_slice src1 mid1 n1
                                                                  ? lem_isSortedBtw_slice src1_cr 1 (n1-mid1)-})
                                                          (src2_r {-? lem_isSortedBtw_slice src2 mid2 n2-})
                                                          dst_r

                                      {-
                                      ? lem_toBag_splitAt mid1 src1
                                      ? lem_toBag_splitAt 1    src1_cr
                                      ? lem_toBag_splitAt mid2 src2
                                      ? lem_toBag_append    dst_l' dst_c'
                                      ? lem_toBag_append    dst''  dst_r'
                                      ? lem_equal_slice_bag src1_c dst_c' 0 (1
                                            ? lma_gs dst_c 0 pivot
                                            ? lem_get_slice src1    mid1 n1 mid1
                                            ? lem_get_slice src1_cr 0 1 0
                                            )-}
                                      -- ? toProof (toBag src1_c === toBag dst_c')
                      in A.append (A.append dst_l' dst_c')  dst_r' 
  where
    n1 = A.size src1
    n2 = A.size src2
    n3 = A.size dst

{-@ reflect binarySearch_func @-} 
{-@ binarySearch_func :: ls:_ -> query:_
                         -> { out:_ | 0 <= out && out <= size ls } @-} 
binarySearch_func :: HasPrimOrd a => A.Array a -> a -> Int -- must be able to return out of bounds
binarySearch_func ls query = binarySearch_func' ls query 0 n
  where 
    n = A.size ls

{-@ reflect binarySearch_func' @-} 
{-@ binarySearch_func' :: ls:_ -> query:_  -> lo:Nat 
                          -> { hi:Nat | lo <= hi && hi <= size ls }
                          -> { out:_ | 0 <= out && out <= size ls } / [hi-lo] @-}
binarySearch_func' :: HasPrimOrd a => A.Array a -> a -> Int -> Int -> Int
binarySearch_func' ls query lo hi = if lo == hi
                               then lo
                               else if query < midElt
                                    then binarySearch_func' ls query lo      mid
                                    else binarySearch_func' ls query (mid+1) hi
  where
    mid    = lo + (hi - lo) `div` 2
    midElt = A.get ls mid  

{-@ lem_binarySearch_func_correct :: { ls:_ | isSorted' ls } -> query:_ 
      -> { pf:_   | ( (binarySearch_func ls query) == 0 
                        || A.get ls ((binarySearch_func ls query)-1) <= query ) &&
                    ( (binarySearch_func ls query) == size ls 
                        || query < A.get ls (binarySearch_func ls query) ) } @-}
lem_binarySearch_func_correct :: HasPrimOrd a => A.Array a -> a -> Proof                                
lem_binarySearch_func_correct ls query = lem_binarySearch_func'_correct ls query 0 n
  where 
    n = A.size ls   

{-@ lem_binarySearch_func'_correct :: { ls:_ | isSorted' ls } -> query:_ 
      -> { lo:Nat | ( lo == 0       || A.get ls (lo-1) <= query ) } 
      -> { hi:Nat | ( hi == size ls || query < A.get ls hi ) &&
                    lo <= hi && hi <= size ls }
      -> { pf:_   | ( (binarySearch_func' ls query lo hi) == 0 
                        || A.get ls ((binarySearch_func' ls query lo hi)-1) <= query ) &&
                    ( (binarySearch_func' ls query lo hi) == size ls 
                        || query < A.get ls (binarySearch_func' ls query lo hi) ) } / [hi-lo] @-}
lem_binarySearch_func'_correct :: HasPrimOrd a => A.Array a -> a -> Int -> Int -> Proof                                
lem_binarySearch_func'_correct ls query lo hi = 
    if lo == hi then ()
    else if query < midElt
         then lem_binarySearch_func'_correct ls query lo      mid
         else lem_binarySearch_func'_correct ls query (mid+1) hi
  where
    mid    = lo + (hi - lo) `div` 2
    midElt = A.get ls mid  

{-@ lem_merge_par_func_sorted :: { xs1:(Array a) | isSorted' xs1 }
      -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2 }
      -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
      -> { pf:_   | isSorted' (merge_par_func xs1 xs2 zs) } / [size xs1] @-} 
lem_merge_par_func_sorted :: HasPrimOrd a => A.Array a -> A.Array a -> A.Array a -> Proof
lem_merge_par_func_sorted src1 src2 dst =
    if A.size dst < goto_seqmerge
    then lem_merge_func_sorted src1 src2 dst 0 0 0 -- merge src1 src2 dst
    else if n1 == 0
         then () -- ??
         else if n2 == 0
              then () -- ??
              else let mid1  = n1 `div` 2
                       pivot = A.get src1 mid1
                       mid2  = binarySearch_func src2 pivot 
                             ? lem_binarySearch_func_correct src2 pivot
                       (src1_l, src1_cr) = A.splitAt mid1 src1
                       (src1_c, src1_r)  = A.splitAt 1    src1_cr
                       (src2_l, src2_r)  = A.splitAt mid2 src2

                       (dst_l, dst_cr)   = A.splitAt (mid1+mid2) dst
                       (dst_c, dst_r)    = A.splitAt 1           dst_cr

                       dst_l'            = merge_par_func src1_l src2_l dst_l
                                         ? lem_merge_par_func_sorted 
                                            (src1_l ? lem_isSortedBtw_slice src1 0 mid1)
                                            (src2_l ? lem_isSortedBtw_slice src2 0 mid2)
                                            dst_l
                       dst_c'            = A.set dst_c 0 pivot
                       dst_r'            = merge_par_func src1_r src2_r dst_r
                                         ? lem_merge_par_func_sorted 
                                            (src1_r ? lem_isSortedBtw_slice src1 mid1 n1
                                                    ? lem_isSortedBtw_slice src1_cr 1 (n1-mid1))
                                            (src2_r ? lem_isSortedBtw_slice src2 mid2 n2)
                                            dst_r
                      in () -- A.append (A.append dst_l' dst_c')  dst_r'               
                            ? lem_isSortedBtw_build_right 
                                (A.append dst_l dst_c) 0  (mid1
                                ? lma_gs dst_c mid1 pivot) 
  where
    n1 = A.size src1
    n2 = A.size src2
    n3 = A.size dst


{- merge_par' on the main branch:
    merge_par' :: { xs1:(Array a) | isSorted' xs1 }
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
{-
{-@ merge_par' :: { t0:_  | isSorted' (fst (fst t0)) && isSorted' (snd (fst t0)) &&
                            token (fst (fst t0)) == token (snd (fst t0)) &&
                            size (fst (fst t0)) + size (snd (fst t0)) == size (snd t0) }
               -> { t:_   | B.union (toBag (fst (fst t0))) (toBag (snd (fst t0))) == toBag (snd t) &&
                            isSorted' (snd t) &&
                            token (fst (fst t)) == token (fst (fst t0)) && 
                            token (snd (fst t)) == token (snd (fst t0)) &&
                            token (snd t)       == token (snd t0) &&
                            left (fst (fst t)) == left (fst (fst t0)) && 
                            right (fst (fst t)) == right (fst (fst t0)) &&
                            left (snd (fst t)) == left (snd (fst t0)) && 
                            right (snd (fst t)) == right (snd (fst t0)) &&
                            left (snd t) == left (snd t0)  && right (snd t) == right (snd t0)  &&
                            size (snd t) == size (snd t0) } / [size (fst (fst t0))] @-} 
merge_par' :: (Show a, HasPrimOrd a) => ((A.Array a, A.Array a), A.Array a) -> ((A.Array a, A.Array a), A.Array a)
merge_par' !((src1, src2), dst) =
  if A.size dst < goto_seqmerge
  then merge src1 src2 dst
  else let !(n1, src1') = A.size2 src1
           !(n2, src2') = A.size2 src2
           !(n3, dst')  = A.size2 dst
        in if n1 == 0
           then let !(src2'1, dst'') = A.copy2_par src2' 0 dst' 0 n2
                 in ((src1', src2'1), dst'') {-? lem_equal_slice_bag  src2'   dst'' 0 (n2
                                                   ? lem_copy_equal_slice src2' 0 dst' 0 n2)-}
           else if n2 == 0
                then let !(src1'1, dst'') = A.copy2_par src1' 0 dst' 0 n1
                      in ((src1'1, src2'), dst'') {-? lem_equal_slice_bag  src1'   dst'' 0 (n1
                                                        ? lem_copy_equal_slice src1' 0 dst' 0 n1)-}
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
                                         merge_par'
                                         ( ( (src1_l ? lem_isSortedBtw_slice src1'1 0  mid1)
                                           , (src2_l ? lem_isSortedBtw_slice src2'1 0  mid2) )
                                         , dst_l )
                                         merge_par'
                                         ( ( (src1_r ? lem_isSortedBtw_slice src1'1 mid1 n1
                                                     ? lem_isSortedBtw_slice src1_cr 1 (n1-mid1))
                                           , (src2_r ? lem_isSortedBtw_slice src2'1 mid2 n2) )
                                         , dst_r )
                         (!((src1_l',src2_l'), dst_l'), !((src1_r',src2_r'), dst_r')) = (left, right)

                         src1_cr'     = A.append src1_c  src1_r'
                         src1'3       = A.append src1_l' src1_cr'
                         src2'3       = A.append src2_l' src2_r'
                         dst''        = A.append dst_l' dst_c'
                         dst'''       = A.append dst''  dst_r' {-}
                                      ? lem_toBag_splitAt mid1 src1
                                      ? lem_toBag_splitAt 1    src1_cr
                                      ? lem_toBag_splitAt mid2 src2
                                      ? lem_toBag_append    dst_l' dst_c'
                                      ? lem_toBag_append    dst''  dst_r'
                                      ? lem_equal_slice_bag src1_c dst_c' 0 (1
                                            ? lma_gs dst_c 0 pivot
                                            ? lem_get_slice src1    mid1 n1 mid1
                                            ? lem_get_slice src1_cr 0 1 0
                                            )-}
                                      -- ? toProof (toBag src1_c === toBag dst_c')
                      in ((src1'3, src2'3), dst''')
-}
{- @ reflect binarySearch @ -} {-
{-@ binarySearch :: { ls:_ | isSorted' ls } -> query:_
                         -> { tup:_ | 0 <= fst tup && fst tup <= size ls &&
                                      snd tup == ls &&
                                      ( fst tup == 0 || A.get ls ((fst tup)-1) <= query ) &&
                                      ( fst tup == size ls || query < A.get ls (fst tup) ) } @-}
binarySearch :: HasPrimOrd a => A.Array a -> a -> (Int, A.Array a) -- must be able to return out of bounds
binarySearch ls query = let (n, ls')  = A.size2 ls
                         in binarySearch' ls' query 0 n
-}

{- @ reflect binarySearch' @ -} {-
{-@ binarySearch' :: { ls:_ | isSorted' ls } -> query:_  
                          -> { lo:Nat | ( lo == 0       || A.get ls (lo-1) <= query ) } 
                          -> { hi:Nat | ( hi == size ls || query < A.get ls hi ) &&
                                        lo <= hi && hi <= size ls }
                          -> { tup:_ | 0 <= fst tup && fst tup <= size ls &&
                                       snd tup == ls &&
                                       ( fst tup == 0 || A.get ls ((fst tup)-1) <= query ) &&
                                       ( fst tup == size ls || query < A.get ls (fst tup) ) } / [hi-lo] @-}
binarySearch' :: HasPrimOrd a => A.Array a -> a -> Int -> Int -> (Int, A.Array a)
binarySearch' ls query lo hi = if lo == hi
                               then (lo, ls)
                               else let mid          = lo + (hi - lo) `div` 2
                                        (midElt, ls') = A.get2 ls mid
                                     in if query < midElt
                                        then binarySearch' ls' query lo      mid
                                        else binarySearch' ls' query (mid+1) hi
                                        -}
{-
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
merge_par :: (Show a, HasPrimOrd a) => A.Array a -> A.Array a -> A.Array a -> (A.Array a, A.Array a)
merge_par !src1 !src2 !dst =
  let !((src1', src2'), dst') = merge_par' ((src1,  src2),  dst)
      src'                    = A.append   src1' src2'
   in (src', dst')   

   -}
