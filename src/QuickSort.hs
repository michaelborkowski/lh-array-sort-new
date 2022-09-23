{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE Strict #-}

module QuickSort where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))

import ProofCombinators
import Array 
import Equivalence
import Order
import Properties

#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
#else
import           Array.List as A
#endif

{-@ quickSort :: xs:(Array a) -> { ys:(Array a) | isSorted' ys && A.size xs == A.size ys &&
                                                                  toBag  xs == toBag  ys } @-}
quickSort :: Ord a => Array a -> Array a 
quickSort xs = quickSortBtw xs 0 (size xs)

{-@ quickSortBtw :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i <= j && j <= A.size xs }
                -> { ys:(Array a) | isSortedBtw ys i j && A.size xs == A.size ys &&
                                    toSlice xs 0 i == toSlice ys 0 i && 
                                    toSlice xs j (A.size xs) == toSlice ys j (A.size xs) &&
                                    toBagBtw xs i j == toBagBtw ys i j } / [j - i] @-}
quickSortBtw :: Ord a => Array a -> Int -> Int -> Array a
quickSortBtw xs i j  =
  if j - i < 2
  then xs
  else let (xs', i_piv) = shuffleBtw xs i j   -- isPartitionedBtw xs' i i_piv j
           xs''         = quickSortBtw xs'  i           i_piv
           xs'''        = quickSortBtw xs'' (i_piv + 1) j
                        ? lem_qs_pres_partition_left  xs'  xs''  i i_piv j
        in xs'''        ? lem_sorted_partitions xs''' i i_piv (j
                              ? lem_equal_slice_sorted xs'' xs''' 0 i i_piv (i_piv+1)
                              ? lem_qs_pres_partition_right xs'' xs''' i i_piv j )
                        ? lem_equal_slice_narrow         xs'  xs'' i_piv j (A.size xs) (A.size xs)
                        ? lem_equal_slice_narrow         xs'  xs'' i_piv i_piv j (A.size xs)
                        ? lem_equal_slice_bag            xs'  xs''       i_piv j
                        ? lem_equal_slice_narrow         xs'' xs''' 0 0 i (i_piv+1)
                        ? lem_equal_slice_narrow         xs'' xs''' 0 i (i_piv+1) (i_piv+1)
                        ? lem_equal_slice_bag            xs'' xs'''   i (i_piv+1)
                        ? lem_toBagBtw_compose           xs'  xs''    i i_piv     j
                        ? lem_toBagBtw_compose           xs'' xs'''   i (i_piv+1) j

{-@ shuffleBtw :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i + 1 < j && j <= A.size xs }
                  -> (Array a, Int)<{\ys ip -> isPartitionedBtw ys i ip j && 
                                               toSlice xs 0 i == toSlice ys 0 i && 
                                               toSlice xs j (A.size xs) == toSlice ys j (A.size xs) &&
                                               toBagBtw xs i j == toBagBtw ys i j &&
                                               i <= ip && ip < j && A.size ys == A.size xs }> @-}
shuffleBtw :: Ord a => Array a -> Int -> Int -> (Array a, Int)
shuffleBtw xs i j = 
  let 
      (piv, xs1) = A.get2 xs (j-1)        -- fix xs[j-1] as the pivot
      {-@ goShuffle :: { zs:(Array a) | get zs (j-1) == piv && A.size zs == A.size xs &&
                                        toBagBtw zs i j == toBagBtw xs i j && 
                                        toSlice xs 0 i == toSlice zs 0 i && 
                                        toSlice xs j (A.size zs) == toSlice zs j (A.size zs)}
                    -> { jl:Int | i <= jl    &&             rangeUpperBound zs i      jl    piv } 
                    -> { jr:Int | jl <= jr+1 && jr < j-1 && rangeLowerBound zs (jr+1) (j-1) piv }
                    -> (Array a, Int)<{\ws ip -> rangeUpperBound ws i      ip    piv && 
                                                 rangeLowerBound ws ip     (j-1) piv &&
                                                 A.size ws == A.size zs && 
                                                 get ws (j-1) == get zs (j-1) &&
                                                 toBagBtw zs i j == toBagBtw ws i j &&
                                                 toBagBtw xs i j == toBagBtw ws i j &&
                                                 toSlice zs 0 i == toSlice ws 0 i && 
                                                 toSlice zs j (A.size zs) == toSlice ws j (A.size zs) &&
                                                 i <= ip && ip < j }> / [jr - jl + 1] @-}
      -- at return, all of ws[i:ip] <= ws[j-1] and all of ws[ip:j-1] > ws[j-1].
      goShuffle zs jl jr    =   -- BOTH bounds inclusive here
        if jl > jr
        then (zs, jl) 
        else let (vl, zs') = A.get2 zs jl in
          if vl <= piv 
          then goShuffle zs' (jl+1 ? lem_rangeProperty_build_right zs (belowPivot (get zs (j-1))) 
                                       i (jl ? toProof (belowPivot (get zs (j-1)) (get zs jl)))) 
                             jr
          else let (vr, zs'') = A.get2 zs jr in
            if vr >  piv  
            then goShuffle zs'' jl     (jr-1)
            else let zs''' = swap zs'' jl jr 
                           ? lem_range_outside_swap zs i jl jr (j-1) piv
                           ? lma_swap        zs   jl jr
                           ? lma_swap_eql zs jl jr (j-1)
                           ? lem_bagBtw_swap zs i jl jr j   
                           ? lem_toSlice_swap  zs i jl jr j 
                  in goShuffle zs''' jl (jr-1)

      (xs', ip)  = goShuffle xs1 i (j-2)  -- BOTH bounds inclusive      
      {-@ xs'' :: { vs:(Array a) | isPartitionedBtw vs i ip j &&
                                   toSlice xs' 0 i == toSlice vs 0 i && 
                                   toSlice xs' j (A.size xs') == toSlice vs j (A.size xs') &&
                                   A.size xs' == A.size vs &&
                                   toBagBtw xs i j == toBagBtw vs i j } @-}
      xs''       = if ip < j-1 
                   then swap xs' ip (j-1) ? lma_swap xs' ip (j-1)
                                          ? lem_bagBtw_swap xs' i ip (j-1) j
                                          ? lem_range_inside_swap xs' ip (j-1)
                                          ? lem_range_outside_swap xs' i ip (j-1) j (get xs' (j-1))
                                          ? lem_toSlice_swap xs' i ip (j-1) j
                   else xs' 
   in (xs'', ip)
--  where

 -- | The remaining definitions and lemmas pertain to the partition property w/r/t the pivot element

{-@ reflect belowPivot @-}
{-@ belowPivot :: a -> a -> Bool @-}
belowPivot :: Ord a => a -> a -> Bool
belowPivot piv v = v <= piv

{-@ reflect abovePivot @-}
{-@ abovePivot :: a -> a -> Bool @-}
abovePivot :: Ord a => a -> a -> Bool
abovePivot piv v = v >  piv

{-@ reflect rangeUpperBound @-}
{-@ rangeUpperBound :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i <= j && j <= size xs }
                                    -> a -> Bool @-}
rangeUpperBound :: Ord a => Array a -> Int -> Int -> a -> Bool
rangeUpperBound xs i j piv = rangeProperty xs i j (belowPivot piv)

{-@ reflect rangeLowerBound @-}
{-@ rangeLowerBound :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i <= j && j <= size xs }
                                    -> a -> Bool @-}
rangeLowerBound :: Ord a => Array a -> Int -> Int -> a -> Bool
rangeLowerBound xs i j piv = rangeProperty xs i j (abovePivot piv)

{-@ reflect isPartitionedBtw @-}
{-@ isPartitionedBtw :: xs:(Array a) -> { i:Int | 0 <= i } -> { i_piv:Int | i <= i_piv }
                                     -> { j:Int | i_piv < j && j <= size xs } -> Bool @-}
isPartitionedBtw :: Ord a => Array a -> Int -> Int -> Int -> Bool
isPartitionedBtw xs i i_piv j = rangeUpperBound xs i           i_piv   (get xs i_piv)   &&
                                rangeLowerBound xs (i_piv + 1) j       (get xs i_piv)   

{-@ ple lem_range_outside_swap @-}
{-@ lem_range_outside_swap :: xs:(Array a) -> { i:Int | 0 <= i } 
                           -> { jl:Int | i <= jl } -> { jr:Int | jl < jr }
                           -> { j:Int  | jr <= j-1 && j <= size xs }
                           -> { piv:a  | rangeUpperBound xs i      jl    piv &&
                                         rangeLowerBound xs (jr+1) j     piv }
                           -> { pf:_ | rangeUpperBound (swap xs jl jr) i      jl    piv &&
                                       rangeLowerBound (swap xs jl jr) (jr+1) j     piv } / [j-i] @-}
lem_range_outside_swap :: Ord a => Array a -> Int -> Int -> Int -> Int -> a -> Proof
lem_range_outside_swap xs i jl jr j piv 
    | i < jl     = () ? lma_swap_eql xs jl jr i
                      ? lem_range_outside_swap xs (i+1) jl jr j     piv 
    | jr+1 < j   = () ? lma_swap_eql xs jl jr (j-1) 
                      ? lem_rangeProperty_right xs (jr+1) j (abovePivot piv)
                      ? lem_range_outside_swap xs i     jl jr (j-1) piv
                      ? lem_rangeProperty_build_right (swap xs jl jr) (abovePivot piv) (jr+1) (j-1)
    | otherwise  = () 

{-@ ple lem_range_inside_swap @-}
{-@ lem_range_inside_swap :: xs:(Array a) -> { jl:Int | 0 <= jl }
                  -> { jr:Int | jl < jr && jr < size xs && 
                                rangeLowerBound xs jl jr (get xs jr) }
                  -> { pf:_ | rangeLowerBound (swap xs jl jr) (jl+1) (jr+1) (get (swap xs jl jr) jl) } @-}
lem_range_inside_swap :: Ord a => Array a -> Int -> Int -> Proof
lem_range_inside_swap xs jl jr = () ? lma_swap xs jl jr 
                                    ? lem_go_inside_swap (jl+1)
  where
    {-@ lem_go_inside_swap :: { jj:Int | jl < jj && jj <= jr &&
                                         rangeLowerBound xs jj jr (get xs jr) } 
                 -> { pf:_ | rangeLowerBound (swap xs jl jr) jj (jr+1) (get (swap xs jl jr) jl) } / [jr-jj] @-}
    lem_go_inside_swap jj 
      | jj < jr    = () ? lma_swap xs jl jr
                        ? lma_swap_eql xs jl jr jj
                        ? lem_go_inside_swap (jj+1) 
      | otherwise  = () ? lma_swap xs jl jr
                         

  -- Lemmas addressing how recursive calls to quickSortBtw preserve the partition property
{-@ ple lem_qs_pres_partition_left @-}
{-@ lem_qs_pres_partition_left  :: xs:(Array a) -> { ys:(Array a) | size xs == size ys }
                                -> { i:Int | 0 <= i } -> { i_piv:Int | i <= i_piv }
                                -> { j:Int | i_piv < j && j <= size xs &&
                                             isPartitionedBtw xs i i_piv j &&
                                             toBagBtw xs i i_piv == toBagBtw ys i i_piv &&
                                             toSlice xs i_piv (size xs) == toSlice ys i_piv (size xs) }                     
                                -> { pf:_  | isPartitionedBtw ys i i_piv j } @-}
lem_qs_pres_partition_left  :: Ord a => Array a -> Array a -> Int -> Int -> Int -> Proof
lem_qs_pres_partition_left  xs ys i i_piv j 
    = () ? lem_bagBtw_pres_rangeProperty xs ys i i_piv      (belowPivot (get xs i_piv))
         ? lem_bagBtw_pres_rangeProperty xs ys (i_piv+1) (j 
         ? lem_equal_slice_narrow     xs ys (i_piv) (i_piv+1) j (size xs)
         ? lem_equal_slice_bag        xs ys         (i_piv+1) j )
                                                            (abovePivot (get xs i_piv))

{-@ ple lem_qs_pres_partition_right @-}
{-@ lem_qs_pres_partition_right  :: xs:(Array a) -> { ys:(Array a) | size xs == size ys }
                                -> { i:Int | 0 <= i } -> { i_piv:Int | i <= i_piv }
                                -> { j:Int | i_piv < j && j <= size xs &&
                                             isPartitionedBtw xs i i_piv j &&
                                             toBagBtw xs (i_piv+1) j == toBagBtw ys (i_piv+1) j &&
                                             toSlice xs 0 (i_piv+1) == toSlice ys 0 (i_piv+1) }                     
                                -> { pf:_  | isPartitionedBtw ys i i_piv j } @-}
lem_qs_pres_partition_right :: Ord a => Array a -> Array a -> Int -> Int -> Int -> Proof
lem_qs_pres_partition_right xs ys i i_piv j 
    = () ? lem_bagBtw_pres_rangeProperty xs ys   i (i_piv   
         ? lem_equal_slice_narrow     xs ys 0 i i_piv (i_piv+1)
         ? lem_equal_slice_bag        xs ys   i i_piv )
                                                           (belowPivot (get xs i_piv))
         ? lem_equal_slice_narrow     xs ys 0 i_piv (i_piv+1) (i_piv+1)
         ? lem_bagBtw_pres_rangeProperty xs ys (i_piv+1) j (abovePivot (get xs i_piv))

{-@ ple lem_sorted_partitions @-}
{-@ lem_sorted_partitions :: xs:(Array a) -> { i:Int | 0 <= i } -> { i_piv:Int | i <= i_piv }
                                          -> { j:Int | i_piv < j && j <= size xs && j - i >= 2 &&
                                                       isSortedBtw xs i         i_piv &&
                                                       isSortedBtw xs (i_piv+1) j &&
                                                       isPartitionedBtw xs i i_piv j } 
                                          -> { pf:_ | isSortedBtw xs i j } @-}
lem_sorted_partitions :: Ord a => Array a -> Int -> Int -> Int -> Proof
lem_sorted_partitions xs i i_piv j 
    | i == i_piv      = () 
    | i_piv + 1 == j  = () ? lem_isSortedBtw_build_right xs i (i_piv 
                           ? lem_rangeProperty_right xs i i_piv (belowPivot (get xs i_piv))
                           ? toProof (belowPivot (get xs i_piv) (get xs (i_piv-1))) )
    | otherwise       = () ? lem_isSortedBtw_compose xs i i_piv (j
                           ? lem_rangeProperty_right xs i i_piv (belowPivot (get xs i_piv))
                           ? toProof (belowPivot (get xs i_piv) (get xs (i_piv-1))) )
