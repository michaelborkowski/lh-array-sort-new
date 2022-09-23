{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection"  @-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}

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
merge' !src1 !src2 !dst i1 i2 j =
  let !(len1, src1') = A.size2 src1
      !(len2, src2') = A.size2 src2 in
  if i1 >= len1
  then
    -- TODO: start using copy2 version here.
    -- let !(src2'1, dst') = A.copy2 src2' i2 dst j (len2-i2+1) in (A.append src1' src2'1, dst')
    let !(src2'1, dst') = copy src2' dst i2 j in (A.append src1' src2'1, dst')
                       {- equivalence -}      ? lem_toBagBtw_compose' src1 0 i1 len1
                                              ? lem_toBagBtw_compose' src2 0 i2 len2
                                              ? lem_toBagBtw_compose' dst' 0 j  (A.size dst')
                                              ? lem_equal_slice_bag   dst dst' 0 j
  else if i2 >= len2
  then
    -- TODO: start using copy2 version here.
    -- let !(src1'1, dst') = A.copy2 src1' i1 dst j (len1-i1+1) in (A.append src1'1 src2', dst')
    let !(src1'1, dst') = copy src1' dst i1 j in (A.append src1'1 src2', dst')
                       {- equivalence -}      ? lem_toBagBtw_compose' src1 0 i1 len1
                                              ? lem_toBagBtw_compose' src2 0 i2 len2
                                              ? lem_toBagBtw_compose' dst' 0 j  (A.size dst')
                                              ? lem_equal_slice_bag   dst dst' 0 j
  else
    let !(v1, src1'1) = A.get2 src1' i1
        !(v2, src2'1) = A.get2 src2' i2 in
    if v1 < v2
    then let dst' = A.set dst j v1
             !(src'', dst'') =  merge' src1'1 src2'1 dst' (i1 + 1) i2 (j + 1
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
             !(src'', dst'') =  merge' src1'1 src2'1 dst' i1 (i2 + 1) (j + 1
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
{-# INLINE merge #-}
{-# SPECIALISE merge :: A.Array Float -> A.Array Float -> A.Array Float -> (A.Array Float, A.Array Float) #-}
{-# SPECIALISE merge :: A.Array Int -> A.Array Int -> A.Array Int -> (A.Array Int, A.Array Int) #-}
merge :: Ord a => A.Array a -> A.Array a -> A.Array a -> (A.Array a, A.Array a)
merge src1 src2 dst = merge' src1 src2 dst 0 0 0   -- the 0's are relative to the current
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


-}


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
