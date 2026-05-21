
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}

module DpsMergeParSeqFallback where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import           Array
import Properties.Equivalence
import Properties.Order

import           Par

import           Linear.Common
#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
#else
import           Array.List as A
#endif
import qualified Array as A

--------------------------------------------------------------------------------
-- | Sequential Fallback Section -- Unlike DpsMerge.hs the slices are not
-- |    assumed to be adjacent/consecutive (also we get to use the parallel
-- |    copy routine)
-- | Proofs for Sortedness and Equivalence
--------------------------------------------------------------------------------

{-@ reflect merge_func @-}
{-@ merge_func :: xs1:(Array a) -> { xs2:(Array a) | token xs1 == token xs2 }
      -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
      -> { i1:Nat | i1 <= size xs1 } -> { i2:Nat | i2 <= size xs2 }
      -> { j:Nat  | i1 + i2 == j && j <= size zs }
      -> { zs':_  | size zs' == size zs && token zs' == token zs &&
                    left zs' == left zs && right zs' == right zs  } / [size zs - j] @-}
merge_func :: HasPrimOrd a => A.Array a -> A.Array a -> A.Array a ->
                Int -> Int -> Int -> A.Array a
merge_func src1 src2 dst i1 i2 j =
    if i1 >= len1
    then A.copy src2 i2 dst j (len2-i2)
    else if i2 >= len2
    then A.copy src1 i1 dst j (len1-i1)
    else if (A.get src1 i1) < (A.get src2 i2)
         then merge_func src1 src2 (A.set dst j (A.get src1 i1)) (i1+1) i2 (j+1)
         else merge_func src1 src2 (A.set dst j (A.get src2 i2)) i1 (i2+1) (j+1)
  where
    len1 = A.size src1
    len2 = A.size src2

{-@ lem_merge_func_untouched :: xs1:(Array a) -> { xs2:(Array a) | token xs1 == token xs2 }
      -> { zs:(Array a) | size xs1 + size xs2 == size zs }
      -> { i1:Nat | i1 <= size xs1 } -> { i2:Nat | i2 <= size xs2 }
      -> { j:Nat  | i1 + i2 == j && j <= size zs }
      -> { pf:_   | toSlice zs 0 j == toSlice (merge_func xs1 xs2 zs i1 i2 j) 0 j }
       / [size zs - j] @-}
lem_merge_func_untouched :: HasPrimOrd a => A.Array a -> A.Array a -> A.Array a ->
                           Int -> Int -> Int -> Proof
lem_merge_func_untouched src1 src2 dst i1 i2 j
    | i1 >= len1  = lem_copy_equal_slice  src2 i2 dst j (len2-i2)
    | i2 >= len2  = lem_copy_equal_slice  src1 i1 dst j (len1-i1)
    | (A.get src1 i1) < (A.get src2 i2)
                  = lem_merge_func_untouched src1 src2
                      (A.set dst j (A.get src1 i1))  (i1+1) i2 (j+1)
                  ? lem_equal_slice_narrow (A.set dst j (A.get src1 i1))
                      (merge_func src1 src2 (A.set dst j (A.get src1 i1)) (i1+1) i2 (j+1))
                      0 0 j (j+1)
                  ? lem_toSlice_set       dst j (A.get src1 i1)
    | otherwise  = lem_equal_slice_narrow (A.set dst j (A.get src2 i2))
                     (merge_func src1 src2 (A.set dst j (A.get src2 i2)) i1 (i2+1) (j+1))
                     0 0 j (j+1 ? lem_toSlice_set       dst j (A.get src2 i2)
                                ? lem_merge_func_untouched src1 src2
                                      (A.set dst j (A.get src2 i2))
                                      i1 (i2+1) (j+1)
                           )
  where
    len1 = A.size src1
    len2 = A.size src2

{-@ lem_merge_func_sorted :: { xs1:(Array a) | isSorted' xs1 }
      -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2 }
      -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
      -> { i1:Nat | i1 <= size xs1 } -> { i2:Nat | i2 <= size xs2 }
      -> { j:Nat  | i1 + i2 == j && j <= size zs &&
                    isSortedBtw zs 0 j &&
                   ( j == 0 || i1 == size xs1 || A.get xs1 i1 >= A.get zs (j-1) ) &&
                   ( j == 0 || i2 == size xs2 || A.get xs2 i2 >= A.get zs (j-1) ) }
      -> { pf:_   | isSortedBtw (merge_func xs1 xs2 zs i1 i2 j) 0 (size zs) } / [size zs - j] @-}
lem_merge_func_sorted :: HasPrimOrd a => A.Array a -> A.Array a -> A.Array a ->
                           Int -> Int -> Int -> Proof
lem_merge_func_sorted src1 src2 dst i1 i2 j
    | i1 >= len1  = lem_isSorted_copy src2 i2 dst (i1+i2) (len2-i2)
    | i2 >= len2  = lem_isSorted_copy src1 i1 dst (i1+len2) (len1-i1)
    | (A.get src1 i1) < (A.get src2 i2)
                  = lem_merge_func_sorted src1 src2
                      (A.set dst j (A.get src1 i1))  (i1+1) i2 (j+1
                        -- WTS: isSortedBtw (A.set dst j (A.get src1 i1)) 0 (j+1)
                        ? lem_toSlice_set       dst j (A.get src1 i1)
                        ? lem_equal_slice_sorted dst
                            (A.set dst j (A.get src1 i1)) 0 0 j j
                        ? lem_isSortedBtw_build_right
                            (A.set dst j (A.get src1 i1)) 0  (j
                            ? lma_gs dst j (A.get src1 i1)
                            ? if j > 0 then lma_gns dst j (j-1) (A.get src1 i1) else ())
                        -- WTS: A.get xs1 (i1+1) >= A.get (A.set dst...) (j+1-1)  and
                        --      A.get xs2  i2    >= A.get (A.set dst...) (j+1-1)    by hypoth
                        ? lma_gs dst j (A.get src1 i1)
                        ? lem_isSortedBtw_narrow src1 0 i1 len1 len1
                      )
    | otherwise   = lem_merge_func_sorted src1 src2
                      (A.set dst j (A.get src2 i2))  i1 (i2+1) (j+1
                        -- WTS: isSortedBtw (A.set dst j (A.get src2 i2)) 0 (j+1)
                        ? lem_toSlice_set       dst j (A.get src2 i2)
                        ? lem_equal_slice_sorted dst
                            (A.set dst j (A.get src2 i2)) 0 0 j j
                        ? lem_isSortedBtw_build_right
                            (A.set dst j (A.get src2 i2)) 0  (j
                            ? lma_gs dst j (A.get src2 i2)
                            ? if j > 0 then lma_gns dst j (j-1) (A.get src2 i2) else ())
                        -- WTS: A.get xs1  i1    >= A.get (A.set dst...) (j+1-1)  and
                        --      A.get xs2 (i2+1) >= A.get (A.set dst...) (j+1-1)
                        ? lma_gs dst j (A.get src2 i2)
                        ? lem_isSortedBtw_narrow src2 0 i2 len2 len2
                      )
  where
    len1 = A.size src1
    len2 = A.size src2

{-@ lem_merge_func_equiv :: xs1:(Array a) -> { xs2:(Array a) | token xs1 == token xs2 }
      -> { zs:(Array a) | size xs1 + size xs2 == size zs }
      -> { i1:Nat | i1 <= size xs1 } -> { i2:Nat | i2 <= size xs2 }
      -> { j:Nat  | i1 + i2 == j && j <= size zs &&
                    B.union (toBagBtw xs1 0 i1) (toBagBtw xs2 0 i2) == toBagBtw zs 0 j }
      -> { pf:_   | B.union (toBag xs1) (toBag xs2) ==
                        toBag (merge_func xs1 xs2 zs i1 i2 j) } / [size zs - j] @-}
lem_merge_func_equiv :: HasPrimOrd a => A.Array a -> A.Array a -> A.Array a ->
                         Int -> Int -> Int -> Proof
lem_merge_func_equiv src1 src2 dst i1 i2 j
    | i1 >= len1  = let dst' = A.copy src2 i2 dst j (len2-i2) in
                        lem_toBagBtw_compose' src1 0 i1 len1
                      ? lem_toBagBtw_compose' src2 0 i2 len2
                      ? lem_toBagBtw_compose' dst' 0 j  (A.size dst')
                      ? lem_equal_slice_bag   dst  dst' 0 (j
                            ? lem_copy_equal_slice src2 i2 dst  j (len2-i2) )
                      ? lem_equal_slice_bag'  src2 dst' i2 len2 j (A.size dst')
    | i2 >= len2  = let dst' = A.copy src1 i1 dst j (len1-i1) in
                        lem_toBagBtw_compose' src1 0 i1 len1
                      ? lem_toBagBtw_compose' src2 0 i2 len2
                      ? lem_toBagBtw_compose' dst' 0 j  (A.size dst')
                      ? lem_equal_slice_bag   dst  dst' 0 (j
                            ? lem_copy_equal_slice src1 i1 dst j (len1-i1) )
                      ? lem_equal_slice_bag'  src1 dst' i1 len1 j (A.size dst')
    | (A.get src1 i1) < (A.get src2 i2)
                 = let dst' = A.set dst j (A.get src1 i1) in
                      lem_merge_func_equiv src1 src2 dst' (i1+1) i2 (j+1
                          ? lem_toBagBtw_right src1 0 (i1+1)
                          ? lem_bag_union (A.get src1 i1) (toBagBtw src1 0 i1)
                                                          (toBagBtw src2 0 i2)
                          ? lem_equal_slice_bag    dst dst'   0 (j
                              ? lem_toSlice_set  dst     j (A.get src1 i1))
                          ? lma_gs dst j (A.get src1 i1)
                          ? lem_toBagBtw_right dst' 0 (j+1)
                        )
    | otherwise  = let dst' = A.set dst j (A.get src2 i2) in
                      lem_merge_func_equiv src1 src2 dst' i1 (i2+1) (j+1
                          ? lem_toBagBtw_right src2 0 (i2+1)
                          ? lem_bag_union (A.get src2 i2) (toBagBtw src1 0 i1)
                                                          (toBagBtw src2 0 i2)
                          ? lem_equal_slice_bag    dst dst'   0 (j
                              ? lem_toSlice_set  dst     j (A.get src2 i2))
                          ? lma_gs dst j (A.get src2 i2)
                          ? lem_toBagBtw_right dst' 0 (j+1)
                        )
  where
    len1 = A.size src1
    len2 = A.size src2

-- these invariant facts are needed to establish invariants of
--    the parallel merge algorithm
{-@ lem_merge_func_inv_left  :: { xs1:(Array a) | isSorted' xs1 }
      -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2 }
      -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
      -> { piv:_  | (size xs1 == 0 || piv <= get xs1 0 ) &&
                    (size xs2 == 0 || piv <= get xs2 0 ) }
      -> { pf:_   | size zs == 0 || piv <= get (merge_func xs1 xs2 zs 0 0 0) 0 } @-}
lem_merge_func_inv_left :: HasPrimOrd a => A.Array a -> A.Array a -> A.Array a -> a -> Proof
lem_merge_func_inv_left src1 src2 dst piv =
    if 0 >= len1 && 0 >= len2 then ()
    else if 0 >= len1
    then lem_copy_equal_slice src2 0 dst 0 len2
    else if 0 >= len2
    then lem_copy_equal_slice src1 0 dst 0 len1
    else if (A.get src1 0) < (A.get src2 0)
         then lma_gs dst 0 (A.get src1 0)
            ? lem_merge_func_untouched src1 src2 (A.set dst 0 (A.get src1 0)) 1 0 1
         else lma_gs dst 0 (A.get src2 0)
            ? lem_merge_func_untouched src1 src2 (A.set dst 0 (A.get src2 0)) 0 1 1
  where
    len1 = A.size src1
    len2 = A.size src2

{-@ lem_merge_func_inv_right  :: { xs1:(Array a) | isSorted' xs1 }
      -> { xs2:(Array a) | isSorted' xs2 && token xs1 == token xs2 }
      -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
      -> { piv:_  | (size xs1 == 0 || get xs1 (size xs1 - 1) <= piv ) &&
                    (size xs2 == 0 || get xs2 (size xs2 - 1) <= piv ) }
      -> { i1:Nat | i1 <= size xs1 } -> { i2:Nat | i2 <= size xs2 }
      -> { j:Nat  | i1 + i2 == j && (size zs == 0 || j < size zs) }
      -> { pf:_   | size zs == 0 || get (merge_func xs1 xs2 zs i1 i2 j) (size zs - 1) <= piv }
       / [size zs - j] @-}
lem_merge_func_inv_right :: HasPrimOrd a => A.Array a -> A.Array a -> A.Array a
                              -> a -> Int -> Int -> Int -> Proof
lem_merge_func_inv_right src1 src2 dst piv i1 i2 j =
    if len3 == 0 then ()
    else if i1 >= len1
    then lem_get_toSlice' src2 (A.copy src2 i2 dst j (len2-i2))
              i2 (len2-1) len2 j (len3-1) (len3
                  ? lem_copy_equal_slice src2 i2 dst  j (len2-i2))
    else if i2 >= len2
    then lem_get_toSlice' src1 (A.copy src1 i1 dst j (len1-i1))
              i1 (len1-1) len1 j (len3-1) (len3
                  ? lem_copy_equal_slice src1 i1 dst j (len1-i1))
    else if (A.get src1 i1) < (A.get src2 i2)
         then lem_merge_func_inv_right src1 src2 (A.set dst j (A.get src1 i1)) piv (i1+1) i2 (j+1)
         else lem_merge_func_inv_right src1 src2 (A.set dst j (A.get src2 i2)) piv i1 (i2+1) (j+1)
  where
    len1 = A.size src1
    len2 = A.size src2
    len3 = A.size dst

--------------------------------------------------------------------------------
-- | Sequential Fallback: Implementation
--------------------------------------------------------------------------------
             -- unneeded:            fst (fst t) == xs1 && snd (fst t) == xs2 &&
{-@ merge' :: i1:Nat -> i2:Nat -> { j:Nat  | i1 + i2 == j }
           -> { xs1:(Array a) | i1 <= size xs1 }
           -> { xs2:(Array a) | token xs1 == token xs2 && i2 <= size xs2 }
           -> { zs:(Array a) | size xs1 + size xs2 == size zs && j <= size zs }
           -> { t:_    | t == ((xs1, xs2), merge_func xs1 xs2 zs i1 i2 j) &&
                         token (fst (fst t)) == token xs1 && token (snd (fst t)) == token xs2 &&
                         left (fst (fst t)) == left xs1 && right (fst (fst t)) == right xs1 &&
                         left (snd (fst t)) == left xs2 && right (snd (fst t)) == right xs2 &&
                         size (snd t) == size zs && token (snd t) == token zs &&
                         left (snd t) == left zs && right (snd t) == right zs  } / [size zs - j] @-}
merge' :: HasPrimOrd a =>
  Int -> Int -> Int ->
  A.Array a -. A.Array a -. A.Array a -.
  ((A.Array a, A.Array a), A.Array a)
merge' i1 i2 j !src1 !src2 !dst = go i1 i2 j src1 src2 dst where
{-@ go :: i1:Nat -> i2:Nat -> { j:Nat  | i1 + i2 == j }
           -> { xs1:(Array a) | i1 <= size xs1 }
           -> { xs2:(Array a) | token xs1 == token xs2 && i2 <= size xs2 }
           -> { zs:(Array a) | size xs1 + size xs2 == size zs && j <= size zs }
           -> { t:_    | t == ((xs1, xs2), merge_func xs1 xs2 zs i1 i2 j) &&
                         token (fst (fst t)) == token xs1 && token (snd (fst t)) == token xs2 &&
                         left (fst (fst t)) == left xs1 && right (fst (fst t)) == right xs1 &&
                         left (snd (fst t)) == left xs2 && right (snd (fst t)) == right xs2 &&
                         size (snd t) == size zs && token (snd t) == token zs &&
                         left (snd t) == left zs && right (snd t) == right zs  } / [size zs - j] @-}
  go :: HasPrimOrd a =>
    Int -> Int -> Int ->
    A.Array a -. A.Array a -. A.Array a -.
    ((A.Array a, A.Array a), A.Array a)
  go !i1 !i2 !j src1 src2 dst =
    let !(Ur len1, !src1') = A.size2 src1
        !(Ur len2, !src2') = A.size2 src2 in
    if i1 >= len1
    then
      let !(src2'1, dst') = A.copy2_par i2 j (len2-i2) src2' dst in ((src1', src2'1), dst')
    else if i2 >= len2
    then
      let !(src1'1, dst') = A.copy2_par i1 j (len1-i1) src1' dst in ((src1'1, src2'), dst')
    else
      let !(Ur v1, !src1'1) = A.get2 i1 src1'
          !(Ur v2, !src2'1) = A.get2 i2 src2' in
      if v1 < v2
      then let !dst' = A.setLin j v1 dst
               !(src_tup, dst'') =  go (i1 + 1) i2 (j + 1) src1'1 src2'1 dst' in
           (src_tup, dst'')
      else let !dst' = A.setLin j v2 dst
               !(src_tup, dst'') =  go i1 (i2 + 1) (j + 1) src1'1 src2'1 dst' in
           (src_tup, dst'')
{-# INLINE merge' #-}

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
merge :: HasPrimOrd a => A.Array a -. A.Array a -. A.Array a -. ((A.Array a, A.Array a), A.Array a)
merge src1 src2 dst = merge' 0 0 0 src1 src2 dst   -- the 0's are relative to the current
                    ? lem_merge_func_sorted src1 src2 dst 0 0 0  -- slices, not absolute indices
                    ? lem_merge_func_equiv  src1 src2 dst 0 0 0
{-# INLINABLE merge #-}
