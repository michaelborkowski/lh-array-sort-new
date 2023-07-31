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
--import           DpsMerge

import           Par

#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
#else
import           Array.List as A
#endif
import qualified Array as A

--------------------------------------------------------------------------------

{-@ reflect merge_func @-}
{-@ merge_func :: xs1:(Array a) -> { xs2:(Array a) | token xs1 == token xs2 }
      -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
      -> { i1:Nat | i1 <= size xs1 } -> { i2:Nat | i2 <= size xs2 }
      -> { j:Nat  | i1 + i2 == j && j <= size zs }
      -> { zs':_  | size zs' == size zs && token zs' == token zs &&
                    left zs' == left zs && right zs' == right zs  } / [size zs - j] @-} 
merge_func :: Ord a => A.Array a -> A.Array a -> A.Array a ->
                Int -> Int -> Int -> A.Array a {- ((A.Array a, A.Array a), A.Array a) -}
merge_func src1 src2 dst i1 i2 j =
    if i1 >= len1
    then {-let dst' =-} A.copy src2 i2 dst j (len2-i2) {- in ((src1, src2), dst')-}     {-
            {- sortedness -}      ? lem_isSorted_copy src2' i2 dst j (len2-i2)          -}
    else if i2 >= len2
    then {-let  dst' =-} A.copy src1 i1 dst j (len1-i1) {-in ((src1, src2), dst')-}     {-
            {- sortedness -}      ? lem_isSorted_copy src1' i1 dst j (len1-i1)          -}
    else if (A.get src1 i1) < (A.get src2 i2)
         then {-let dst' =-} merge_func src1 src2 (A.set dst j (A.get src1 i1)) (i1+1) i2 (j+1)
              {-in ((src1, src2), dst')-}                                             {-
             -- !(src_tup, dst'') =  merge' src1'1 src2'1 dst' (i1 + 1) i2 (j + 1
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
              --                     ) in (src_tup, dst'')                             -}
          else {-let dst' =-} merge_func src1 src2 (A.set dst j (A.get src2 i2)) i1 (i2+1) (j+1)
               {-in ((src1, src2), dst')-}                                             {-
               -- =  merge' src1'1 src2'1 dst' i1 (i2 + 1) (j + 1
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
               --                    ) in (src_tup, dst'')                             -}
  where 
    len1 = A.size src1
    len2 = A.size src2

{-@ lem_merge_func_untouched :: xs1:(Array a) -> { xs2:(Array a) | token xs1 == token xs2 }
      -> { zs:(Array a) | size xs1 + size xs2 == size zs }
      -> { i1:Nat | i1 <= size xs1 } -> { i2:Nat | i2 <= size xs2 }
      -> { j:Nat  | i1 + i2 == j && j <= size zs }
      -> { pf:_   | toSlice zs 0 j == toSlice (merge_func xs1 xs2 zs i1 i2 j) 0 j } 
       / [size zs - j] @-} 
lem_merge_func_untouched :: Ord a => A.Array a -> A.Array a -> A.Array a ->
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
lem_merge_func_sorted :: Ord a => A.Array a -> A.Array a -> A.Array a ->
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
lem_merge_func_equiv :: Ord a => A.Array a -> A.Array a -> A.Array a ->
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

{- merge' signature on the main branch was
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
{-
-- DPS merge -- non-parallel, non-consecutive source slices, return them unchanged
             -- unneeded:            fst (fst t) == xs1 && snd (fst t) == xs2 &&
{-@ merge' :: xs1:(Array a) -> { xs2:(Array a) | token xs1 == token xs2 }
           -> { zs:(Array a) | size xs1 + size xs2 == size zs }
           -> { i1:Nat | i1 <= size xs1 } -> { i2:Nat | i2 <= size xs2 }
           -> { j:Nat  | i1 + i2 == j && j <= size zs }
           -> { t:_    | t == ((xs1, xs2), merge_func xs1 xs2 zs i1 i2 j) &&
                         token (fst (fst t)) == token xs1 && token (snd (fst t)) == token xs2 &&
                         left (fst (fst t)) == left xs1 && right (fst (fst t)) == right xs1 &&
                         left (snd (fst t)) == left xs2 && right (snd (fst t)) == right xs2 &&
                         size (snd t) == size zs && token (snd t) == token zs &&
                         left (snd t) == left zs && right (snd t) == right zs  } / [size zs - j] @ -}
merge' :: HasPrimOrd a =>
  A.Array a -> A.Array a -> A.Array a ->
  Int -> Int -> Int ->
  ((A.Array a, A.Array a), A.Array a)
merge' !src1 !src2 !dst i1 i2 j =
  let !(len1, src1') = A.size2 src1
      !(len2, src2') = A.size2 src2 in
  if i1 >= len1
  then
    let !(src2'1, dst') = A.copy2_par src2' i2 dst j (len2-i2) in ((src1', src2'1), dst')
{-          {- sortedness -}      ? lem_isSorted_copy src2' i2 dst j (len2-i2) -}
  else if i2 >= len2
  then
    let !(src1'1, dst') = A.copy2_par src1' i1 dst j (len1-i1) in ((src1'1, src2'), dst')
{-          {- sortedness -}      ? lem_isSorted_copy src1' i1 dst j (len1-i1) -}
  else
    let !(v1, src1'1) = A.get2 src1' i1
        !(v2, src2'1) = A.get2 src2' i2 in
    if v1 < v2
    then let dst' = A.set dst j v1
             !(src_tup, dst'') =  merge' src1'1 src2'1 dst' (i1 + 1) i2 (j + 1
{-                  {- eq -}          ? lem_toBagBtw_right src1 0 (i1+1)
                                      ? lem_bag_union v1 (toBagBtw src1 0 i1) (toBagBtw src2 0 i2)
                                      ? lem_equal_slice_bag    dst dst'   0 (j
                                          ? lem_toSlice_set    dst     j v1)
                                      ? lma_gs dst j v1
                                      ? lem_toBagBtw_right dst' 0 (j+1)
                    {- sor -}         ? lem_isSortedBtw_narrow src1 0 i1 len1 len1
                                      ? lem_equal_slice_sorted dst   dst'  0 0 j j
                                      ? lem_isSortedBtw_build_right  dst'  0 (j
                                            ? if j > 0 then lma_gns dst   j (j-1) v1 else ()) -}
                                 ) in
         (src_tup, dst'') -- ? lem_equal_slice_narrow dst' dst'' 0 0 j (j+1)
    else let dst' = A.set dst j v2
             !(src_tup, dst'') =  merge' src1'1 src2'1 dst' i1 (i2 + 1) (j + 1
{-                                    ? lem_toBagBtw_right src2 0 (i2+1)
                                      ? lem_bag_union v2 (toBagBtw src1 0 i1) (toBagBtw src2 0 i2)
                                      ? lem_equal_slice_bag    dst dst'   0 (j
                                          ? lem_toSlice_set    dst     j v2)
                                      ? lma_gs dst j v2
                                      ? lem_toBagBtw_right dst' 0 (j+1)
                    {- sor -}         ? lem_isSortedBtw_narrow src2 0 i2 len2 len2
                                      ? lem_equal_slice_sorted dst   dst'  0 0 j j
                                      ? lem_isSortedBtw_build_right  dst'  0 (j
                                            ? if j > 0 then lma_gns dst   j (j-1) v2 else ()) -}
                                 ) in
         (src_tup, dst'') -- ? lem_equal_slice_narrow dst' dst'' 0 0 j (j+1)
-}

{-
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
merge :: HasPrimOrd a => A.Array a -> A.Array a -> A.Array a -> ((A.Array a, A.Array a), A.Array a)
merge src1 src2 dst = merge' src1 src2 dst 0 0 0   -- the 0's are relative to the current
                                                   --   slices, not absolute indices


{- on the branch (also Ord a => instead)
                    ? lem_merge_func_sorted src1 src2 dst 0 0 0  -- slices, not absolute indices
                    ? lem_merge_func_equiv  src1 src2 dst 0 0 0 
-}

-}

goto_seqmerge :: Int
goto_seqmerge = 4096

{- 
{-# INLINE merge_par'' #-}
merge_par'' :: (Show a, HasPrimOrd a) => (A.Array a, A.Array a, A.Array a) -> ((A.Array a, A.Array a), A.Array a)
merge_par'' (src1, src2, dst) = merge_par' src1 src2 dst
-}

-- unlike in merge, these may not have consecutive slices of the source array
-- input tuple is ((xs1, xs2), zs)    -- TODO: condense the post-conditions

{-

{-@ reflect merge_par_func @-}
{-@ merge_par_func :: xs1:(Array a) -> { xs2:(Array a) | token xs1 == token xs2 }
      -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
      -> { i1:Nat | i1 <= size xs1 } -> { i2:Nat | i2 <= size xs2 }
      -> { j:Nat  | i1 + i2 == j && j <= size zs }
      -> { zs':_  | size zs' == size zs && token zs' == token zs &&
                    left zs' == left zs && right zs' == right zs  } / [size zs - j] @-} 
merge_par_func :: Ord a => A.Array a -> A.Array a -> A.Array a ->
                              A.Array a {- ((A.Array a, A.Array a), A.Array a) -}

                              -}

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
