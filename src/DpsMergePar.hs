
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}

module DpsMergePar where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import           Array
import Properties.Equivalence
import Properties.Order
import           DpsMergeParSeqFallback

import           Par

#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
import           Control.DeepSeq ( NFData(..) )
#else
import           Array.List as A
#endif
import qualified Array as A

--------------------------------------------------------------------------------
-- | Parallel Merge -- Proofs for Sortedness and Equivalence
--------------------------------------------------------------------------------

{-@ reflect goto_seqmerge @-}
goto_seqmerge :: Int
#ifdef MUTABLE_ARRAYS
goto_seqmerge = 4096
#else 
goto_seqmerge = 2 
#endif

-- unlike in merge, these may not have consecutive slices of the source array
-- input tuple is ((xs1, xs2), zs)    -- TODO: condense the post-conditions

-- save sorted and equiv for the lemmas -- only output the destination
{-@ reflect merge_par_func @-}
{-@ merge_par_func :: xs1:(Array a) -> { xs2:(Array a) | token xs1 == token xs2 }
      -> { zs :(Array a) | size xs1 + size xs2 == size zs }
      -> { zs':_  | size zs' == size zs && token zs' == token zs &&
                    left zs' == left zs && right zs' == right zs  } / [size xs1] @-} 
merge_par_func :: HasPrimOrd a => A.Array a -> A.Array a -> A.Array a -> A.Array a 
merge_par_func src1 src2 dst  =
    if A.size dst < goto_seqmerge 
    then merge_func src1 src2 dst 0 0 0 -- merge src1 src2 dst
    else if n1 == 0
         then A.copy src2 0 dst 0 n2 
         else if n2 == 0
              then A.copy src1 0 dst 0 n1  
              else let mid1  = n1 `div` 2
                       pivot = A.get src1 mid1
                       mid2  = binarySearch_func src2 pivot -- src2[mid2] must <= all src1[mid1+1..]
                                                            --            must >= all src1[0..mid1]
                       (src1_l, src1_cr) = A.splitAt mid1 src1
                       (src1_c, src1_r)  = A.splitAt 1    src1_cr
                       (src2_l, src2_r)  = A.splitAt mid2 src2

                       (dst_l, dst_cr)   = A.splitAt (mid1+mid2) dst
                       (dst_c, dst_r)    = A.splitAt 1           dst_cr

                       dst_l'            = merge_par_func src1_l src2_l dst_l
                       dst_c'            = A.set dst_c 0 pivot
                       dst_r'            = merge_par_func src1_r src2_r dst_r
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


{-@ lem_merge_par_func_inv_left  :: { xs1:(Array a) | isSorted' xs1 }
      -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2 }
      -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
      -> { piv:_  | (size xs1 == 0 || piv <= get xs1 0 ) &&
                    (size xs2 == 0 || piv <= get xs2 0 ) }
      -> { pf:_   | size zs == 0 || piv <= get (merge_par_func xs1 xs2 zs) 0 } / [size xs1] @-}
lem_merge_par_func_inv_left :: HasPrimOrd a => A.Array a -> A.Array a -> A.Array a -> a -> Proof
lem_merge_par_func_inv_left src1 src2 dst piv = 
    if A.size dst < goto_seqmerge
    then lem_merge_func_inv_left src1 src2 dst piv
    else if n1 == 0
         then lem_copy_equal_slice src2 0 dst 0 n2 
         else if n2 == 0
              then lem_copy_equal_slice src1 0 dst 0 n1 
              else let mid1  = n1 `div` 2
                       pivot = A.get src1 mid1
                       mid2  = binarySearch_func src2 pivot 
                       (src1_l, src1_cr) = A.splitAt mid1 src1
                       (src1_c, src1_r)  = A.splitAt 1    src1_cr
                       (src2_l, src2_r)  = A.splitAt mid2 src2

                       (dst_l, dst_cr)   = A.splitAt (mid1+mid2) dst
                       (dst_c, dst_r)    = A.splitAt 1           dst_cr

                       dst_l'            = merge_par_func src1_l src2_l dst_l
                       dst_c'            = A.set dst_c 0 pivot
                       dst_r'            = merge_par_func src1_r src2_r dst_r
                      in if size dst_l > 0 
                         then lem_get_append_left (A.append dst_l' dst_c')  dst_r' 0
                            ? lem_get_append_left dst_l' dst_c' 0
                            ? lem_merge_par_func_inv_left 
                                  (src1_l ? lem_isSortedBtw_slice src1 0 mid1)
                                  (src2_l ? lem_isSortedBtw_slice src2 0 mid2) dst_l (piv
                                      ? (if A.size src1_l > 0 then lem_get_slice src1 0 mid1 0 else ())
                                      ? (if A.size src2_l > 0 then lem_get_slice src2 0 mid2 0 else ()) )
                         else lem_get_append_left (A.append dst_l' dst_c')  dst_r' 0
                            ? lem_get_append_right dst_l' dst_c' 0
                            ? lma_gs dst_c 0 pivot
  where
    n1 = A.size src1
    n2 = A.size src2
    n3 = A.size dst

{-@ lem_merge_par_func_inv_right  :: { xs1:(Array a) | isSorted' xs1 }
      -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2 }
      -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
      -> { piv:_  | (size xs1 == 0 || get xs1 (size xs1 - 1) <= piv ) &&
                    (size xs2 == 0 || get xs2 (size xs2 - 1) <= piv ) }
      -> { pf:_   | size zs == 0 || get (merge_par_func xs1 xs2 zs) (size zs - 1) <= piv } / [size xs1] @-}
lem_merge_par_func_inv_right :: HasPrimOrd a => A.Array a -> A.Array a -> A.Array a -> a -> Proof
lem_merge_par_func_inv_right src1 src2 dst piv =    
    if A.size dst < goto_seqmerge
    then lem_merge_func_inv_right src1 src2 dst piv 0 0 0
    else if n1 == 0
         then toProof ( get (merge_par_func src1 src2 dst) (n3 - 1)
                    === get (A.copy src2 0 dst 0 n2) (n2 - 1)
                      ? lem_get_toSlice src2 (A.copy src2 0 dst 0 n2) 0 (n2-1) (n2
                            ? lem_copy_equal_slice src2 0 dst 0 n2)
                    === get src2 (n2 - 1) )  
         else if n2 == 0
              then toProof ( get (merge_par_func src1 src2 dst) (n3 - 1)
                         === get (A.copy src1 0 dst 0 n1) (n1 - 1)
                           ? lem_get_toSlice src1 (A.copy src1 0 dst 0 n1) 0 (n1-1) (n1
                                ? lem_copy_equal_slice src1 0 dst 0 n1)
                         === get src1 (n1 - 1) ) 
              else let mid1  = n1 `div` 2
                       pivot = A.get src1 mid1
                       mid2  = binarySearch_func src2 pivot 
                       (src1_l, src1_cr) = A.splitAt mid1 src1
                       (src1_c, src1_r)  = A.splitAt 1    src1_cr
                       (src2_l, src2_r)  = A.splitAt mid2 src2

                       (dst_l, dst_cr)   = A.splitAt (mid1+mid2) dst
                       (dst_c, dst_r)    = A.splitAt 1           dst_cr

                       dst_l'            = merge_par_func src1_l src2_l dst_l
                       dst_c'            = A.set dst_c 0 pivot
                       dst_r'            = merge_par_func src1_r src2_r dst_r
                      in if size dst_r > 0 
                         then lem_get_append_right (A.append dst_l' dst_c')  dst_r' (n3 - 1)
                            ? lem_merge_par_func_inv_right 
                                (src1_r ? lem_isSortedBtw_slice src1 mid1 n1
                                        ? lem_isSortedBtw_slice src1_cr 1 (n1-mid1))
                                (src2_r ? lem_isSortedBtw_slice src2 mid2 n2)
                                dst_r (piv ? (if A.size src1_r > 0 
                                              then lem_get_slice src1 mid1 n1 (n1-1) 
                                                 ? lem_get_slice src1_cr 1 (n1-mid1) (n1-mid1-1) 
                                              else ())
                                           ? (if A.size src2_r > 0 
                                              then lem_get_slice src2 mid2 n2 (n2-1) else ()) )
                         else lem_get_append_left (A.append dst_l' dst_c')  dst_r' (mid1 + mid2)
                            ? lem_get_append_right dst_l' dst_c' (mid1 + mid2)
                            ? lma_gs dst_c 0 pivot
  where
    n1 = A.size src1
    n2 = A.size src2
    n3 = A.size dst

{-@ lem_merge_par_func_equiv :: xs1:(Array a) 
      -> { xs2:(Array a) | token xs1 == token xs2 }
      -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
      -> { pf:_   | B.union (toBag xs1) (toBag xs2) ==
                        toBag (merge_par_func xs1 xs2 zs) } / [size xs1] @-} 
lem_merge_par_func_equiv :: HasPrimOrd a => A.Array a -> A.Array a -> A.Array a -> Proof
lem_merge_par_func_equiv src1 src2 dst =
    if n3 < goto_seqmerge 
    then lem_merge_func_equiv src1 src2 dst 0 0 0 -- merge src1 src2 dst
    else if n1 == 0
         then lem_equal_slice_bag  src2 (A.copy src2 0 dst 0 n2) 0 (n2
                  ? lem_copy_equal_slice src2 0 dst 0 n2 )
         else if n2 == 0
              then   lem_equal_slice_bag src1 (A.copy src1 0 dst 0 n1) 0 (n1
                       ? lem_copy_equal_slice src1 0 dst 0 n1)
              else let mid1  = n1 `div` 2
                       pivot = A.get src1 mid1
                       mid2  = binarySearch_func src2 pivot -- src2[mid2] must <= all src1[mid1+1..]
                                                            --            must >= all src1[0..mid1]
                       (src1_l, src1_cr) = A.splitAt mid1 src1
                       (src1_c, src1_r)  = A.splitAt 1    src1_cr
                       (src2_l, src2_r)  = A.splitAt mid2 src2

                       (dst_l, dst_cr)   = A.splitAt (mid1+mid2) dst
                       (dst_c, dst_r)    = A.splitAt 1           dst_cr

                       dst_l'            = merge_par_func src1_l src2_l dst_l
                       dst_c'            = A.set dst_c 0 pivot
                       dst_r'            = merge_par_func src1_r src2_r dst_r

                     in lem_toBag_splitAt mid1 src1
                      ? lem_toBag_splitAt 1    src1_cr
                      ? lem_toBag_splitAt mid2 src2
                      ? lem_toBag_append    dst_l'                    dst_c'
                      ? lem_toBag_append    (A.append dst_l' dst_c')  dst_r'
                      ? lem_merge_par_func_equiv src1_l src2_l dst_l
                      ? lem_equal_slice_bag src1_c dst_c' 0 (1
                            ? lma_gs dst_c 0 pivot
                            ? lem_get_slice src1    mid1 n1 mid1
                            ? lem_get_slice src1_cr 0 1 0   )
                      ? lem_merge_par_func_equiv src1_r src2_r dst_r
  where
    n1 = A.size src1
    n2 = A.size src2
    n3 = A.size dst  

{-@ lem_merge_par_func_sorted :: { xs1:(Array a) | isSorted' xs1 }
      -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2 }
      -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
      -> { pf:_   | isSortedBtw (merge_par_func xs1 xs2 zs) 0 (size zs) } / [size xs1] @-} 
lem_merge_par_func_sorted :: HasPrimOrd a => A.Array a -> A.Array a -> A.Array a -> Proof
lem_merge_par_func_sorted src1 src2 dst =
    if n3 < goto_seqmerge 
    then lem_merge_func_sorted src1 src2 dst 0 0 0 
    else if n1 == 0
         then lem_isSorted_copy src2 0 dst 0 n2
         else if n2 == 0
              then lem_isSorted_copy src1 0 dst 0 n1
              else let mid1  = n1 `div` 2
                       pivot = A.get src1 mid1
                       mid2  = binarySearch_func src2 pivot 
                       (src1_l, src1_cr) = A.splitAt mid1 src1
                       (src1_c, src1_r)  = A.splitAt 1    src1_cr
                       (src2_l, src2_r)  = A.splitAt mid2 src2

                       (dst_l, dst_cr)   = A.splitAt (mid1+mid2) dst
                       (dst_c, dst_r)    = A.splitAt 1           dst_cr

                       dst_l'            = merge_par_func src1_l src2_l dst_l

                       dst_c'            = A.set dst_c 0 pivot
                       dst_r'            = merge_par_func src1_r src2_r dst_r
                      in lem_isSorted_append   -- A.append (A.append dst_l' dst_c')  dst_r'     
                            (A.append (dst_l' 
                                         ? lem_merge_par_func_sorted 
                                            (src1_l ? lem_isSortedBtw_slice src1 0 mid1)
                                            (src2_l ? lem_isSortedBtw_slice src2 0 mid2)
                                            dst_l )
                                dst_c'  ? lem_isSorted_append dst_l' (dst_c'
                                        ? lem_merge_par_func_inv_right src1_l src2_l dst_l (pivot
    {- src1_l[mid1-1] <= pivot -}           ? lem_isSortedBtw_narrow src1 0 (max (mid1-1) 0) n1 n1
                                            ? (if (size src1_l == 0) then ()
                                               else lem_get_slice src1    0    mid1 (mid1-1) )  
                                            ? lem_get_slice src1    mid1 n1   mid1
                                            ? lem_get_slice src1_cr 0    1    0  
                                            ? (if mid2>0 then lem_get_slice src2 0 mid2 (mid2-1) else ())
                                            ? lem_binarySearch_func_correct src2 pivot
                                            ? lma_gs dst_c 0 pivot)))
                            (dst_r' ? lem_get_append_right dst_l' dst_c' (mid1 + mid2)
                                    ? lem_merge_par_func_sorted 
                                          (src1_r ? lem_isSortedBtw_slice src1 mid1 n1
                                                  ? lem_isSortedBtw_slice src1_cr 1 (n1-mid1))
                                          (src2_r ? lem_isSortedBtw_slice src2 mid2 n2)
                                          dst_r
                                    ? lem_merge_par_func_inv_left src1_r src2_r dst_r (pivot
    {- WTS: pivot < dst_r'[0] -}          ? lem_binarySearch_func_correct src2 pivot
                                          ? lma_gs dst_c 0 pivot      
    {-pivot < src1_r[0] -}                ? lem_isSortedBtw_narrow src1 0 mid1 n1 n1
                                          ? lem_get_slice src1    mid1 n1 mid1
                                          ? lem_get_slice src1_cr 0    1  0 
                                          ? (if mid1 + 1 < n1 then lem_get_slice src1    mid1 n1 (mid1+1) else ())
                                          ? (if mid1 + 1 < n1 then lem_get_slice src1_cr 1    (n1-mid1) 1 else ())
    {-pivot < src2[mid2] = src2_r[0]-}    ? (if mid2 < n2 then lem_get_slice src2 mid2 n2 mid2 else ())
                                    )
                            )
  where
    n1 = A.size src1
    n2 = A.size src2
    n3 = A.size dst
    
--------------------------------------------------------------------------------
-- | Parallel Merge: Implementation
--------------------------------------------------------------------------------    

{-@ merge_par' :: xs1:(Array a) -> { xs2:(Array a) | token xs1 == token xs2 }
      -> { zs :(Array a) | size xs1 + size xs2 == size zs }
      -> { t:_   | snd t == merge_par_func xs1 xs2 zs &&
                   token (fst (fst t)) == token xs1 && token (snd (fst t)) == token xs2 &&
                   left (fst (fst t)) == left xs1 && right (fst (fst t)) == right xs1 &&
                   left (snd (fst t)) == left xs2 && right (snd (fst t)) == right xs2 &&
                   size (snd t) == size zs && token (snd t) == token zs &&
                   left (snd t) == left zs && right (snd t) == right zs  } / [size xs1] @-} 
#ifdef MUTABLE_ARRAYS
merge_par' :: (Show a, HasPrimOrd a, NFData a) =>
#else
merge_par' :: (Show a, HasPrimOrd a) =>
#endif                   
   A.Array a -> A.Array a -> A.Array a -> ((A.Array a, A.Array a), A.Array a)
merge_par' !src1 !src2 !dst =
  if A.size dst < goto_seqmerge
  then merge' src1 src2 dst 0 0 0
     ? toProof (merge_par_func src1 src2 dst === merge_func src1 src2 dst 0 0 0)
  else let !(n1, src1') = A.size2 src1
           !(n2, src2') = A.size2 src2
           !(n3, dst')  = A.size2 dst
        in if n1 == 0
           then let !(src2'1, dst'') = A.copy2_par src2' 0 dst' 0 n2
                 in ((src1', src2'1), dst'') 
           else if n2 == 0
                then let !(src1'1, dst'') = A.copy2_par src1' 0 dst' 0 n1
                      in ((src1'1, src2'), dst'') 
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

                         (!((src1_l',src2_l'), dst_l'), !((src1_r',src2_r'), dst_r')) 
                            = (merge_par' src1_l src2_l dst_l) .||. (merge_par' src1_r src2_r dst_r)
                                                                              {-
                         (left, right) = tuple2 (merge_par' src1_l src2_l) dst_l
--                                         ( ( (src1_l ? lem_isSortedBtw_slice src1'1 0  mid1)
--                                           , (src2_l ? lem_isSortedBtw_slice src2'1 0  mid2) )
--                                         , dst_l )
                                                  (merge_par' src1_r src2_r) dst_r
--                                         ( ( (src1_r ? lem_isSortedBtw_slice src1'1 mid1 n1
--                                                     ? lem_isSortedBtw_slice src1_cr 1 (n1-mid1))
--                                           , (src2_r ? lem_isSortedBtw_slice src2'1 mid2 n2) )
--                                         , dst_r )
                        -}
                         src1_cr'     = A.append src1_c  src1_r'
                         src1'3       = A.append src1_l' src1_cr'
                         src2'3       = A.append src2_l' src2_r'
                         dst''        = A.append dst_l' dst_c'
                         dst'''       = A.append dst''  dst_r' 
                      in ((src1'3, src2'3), dst''') 

{-@ binarySearch :: ls:_ -> query:_
                         -> { tup:_ | 0 <= fst tup && fst tup <= size ls &&
                                      snd tup == ls && tup = (binarySearch_func ls query, ls) } @-}
binarySearch :: HasPrimOrd a => A.Array a -> a -> (Int, A.Array a) -- must be able to return out of bounds
binarySearch ls query = let (n, ls')  = A.size2 ls
                         in binarySearch' ls' query 0 n

{-@ binarySearch' :: ls:_ -> query:_  -> lo:Nat 
                          -> { hi:Nat | lo <= hi && hi <= size ls }
                          -> { tup:_ | 0 <= fst tup && fst tup <= size ls &&
                                       snd tup == ls && 
                                      tup = (binarySearch_func' ls query lo hi, ls) } / [hi-lo] @-}
binarySearch' :: HasPrimOrd a => A.Array a -> a -> Int -> Int -> (Int, A.Array a)
binarySearch' ls query lo hi = if lo == hi
                               then (lo, ls)
                               else let mid          = lo + (hi - lo) `div` 2
                                        (midElt, ls') = A.get2 ls mid
                                     in if query < midElt
                                        then binarySearch' ls' query lo      mid
                                        else binarySearch' ls' query (mid+1) hi
                                        
{-@ merge_par :: { xs1:(Array a) | isSorted' xs1 }
              -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2 && right xs1 == left xs2 }
              -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
              -> { t:_           | B.union (toBag xs1) (toBag xs2) == toBag (snd t) &&
                                   isSorted' (snd t) &&
                                   token (fst t) == token xs1 && token (snd t) == token zs &&
                                   left (fst t) == left xs1 && right (fst t) == right xs2 &&
                                   left (snd t) == left zs  && right (snd t) == right zs  &&
                                   size (fst t) == size xs1 + size xs2 &&
                                   size (snd t) == size zs } / [size xs1] @-} 
{-# INLINE merge_par #-}
{-# SPECIALISE merge_par :: A.Array Float -> A.Array Float -> A.Array Float -> (A.Array Float, A.Array Float) #-}
{-# SPECIALISE merge_par :: A.Array Int -> A.Array Int -> A.Array Int -> (A.Array Int, A.Array Int) #-}
#ifdef MUTABLE_ARRAYS
merge_par :: (Show a, HasPrimOrd a, NFData a) =>
#else
merge_par :: (Show a, HasPrimOrd a) =>
#endif                   
   A.Array a -> A.Array a -> A.Array a -> (A.Array a, A.Array a)
merge_par !src1 !src2 !dst =
  let !((src1', src2'), dst') = merge_par' src1  src2  dst
      src'                    = A.append   src1' src2'
   in (src', dst')   
                    ? lem_merge_par_func_sorted src1 src2 dst 
                    ? lem_merge_par_func_equiv  src1 src2 dst    
