{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection"  @-}

{-# LANGUAGE CPP #-}

module DpsMerge where

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
                    A.size (snd t) == A.size dst } / [size src - i] @-}
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
                              ? lem_isSortedBtw_build_right  dst'1 0 (j 
                                   ? if j > 0 then lma_gns       dst   j (j-1) v else ())  
                           ) in
    (src'2, dst'2)     ? toProof ( toBagBtw src i len
            {- equivalence -}  === B.put v (toBagBtw src (i+1) len)
                                 ? lem_get_toSlice dst'1 dst'2 0 j (j+1)
                               === B.put (A.get dst'2 j) (toBagBtw dst'2 (j+1) (A.size dst)) 
                               === toBagBtw dst'2 j (A.size dst) )
                       ? lem_equal_slice_narrow dst'1 dst'2 0 0 j (j+1) 
  else (src', dst)

-- DPS merge
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
                         size (snd t) == size zs } / [size zs - j] @-}
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
