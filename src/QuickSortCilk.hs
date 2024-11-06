
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorder"  @-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE Strict #-}


module QuickSortCilk where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))

import ProofCombinators
import Array
import ArrayOperations
import Properties.Equivalence
import Properties.Order
import Properties.RangeProperties

import Insertion

#ifdef MUTABLE_ARRAYS
import qualified Unsafe.Linear as Unsafe
import           Array.Mutable as A
#else
import qualified Linear.Unsafe as Unsafe
import           Array.List as A
#endif
import qualified Array as A

#define KILO 1024
#define MERGESIZE (2*KILO)
#define QUICKSIZE (2*KILO)
#define INSERTIONSIZE 20

--------------------------------------------------------------------------------
-- | It's QuickSort, but this one falls back to insertion sort eventually
--------------------------------------------------------------------------------

{-@ quickSort :: xs:(Array a) -> { ys:_ | toBag xs == toBag ys &&  isSorted' ys &&
                                          A.size xs == A.size ys && token xs == token ys } @-}
quickSort :: (HasPrimOrd a, Show a) => Array a -> Array a  -- TODO: linearize this later
quickSort xs = let (Ur n, xs1) = A.size2 xs in quickSortBtw 0 n xs1

{-@ quickSortBtw :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i <= j && j <= A.size xs }
                -> { ys:(Array a) | isSortedBtw ys i j && A.size xs == A.size ys &&
                                    toSlice xs 0 i == toSlice ys 0 i &&
                                    toSlice xs j (A.size xs) == toSlice ys j (A.size xs) &&
                                    toBagBtw xs i j == toBagBtw ys i j } / [j - i] @-}
quickSortBtw :: HasPrimOrd a => Array a -> Int -> Int -> Array a
quickSortBtw xs i j  =
  if j - i < 2               then xs            else
  if j - i <= INSERTIONSIZE  
  then let (xs_l, xs_cr) = A.splitAt i     xs 
           (xs_c, xs_r)  = A.splitAt (j-i) xs_cr
           xs_c'         = isort_top' xs_c
           xs_cr'        = A.append   xs_c' xs_r
          in A.append xs_l xs_cr'
           ? toProof ( True
                   === isSortedBtw xs_c' 0 (j-i)      
                     ? lem_isSortedBtw_from_left_append  xs_c' xs_r   0 (j-i) 
                   === isSortedBtw xs_cr' 0 (j-i) 
                     ? lem_isSortedBtw_from_right_append xs_l  xs_cr' i j
                   === isSortedBtw (A.append xs_l xs_cr') i j
           )
           ? lem_toBagBtw_slice xs_cr 0 (j-i) 0 (j-i)
           ? lem_toBagBtw_slice xs i (A.size xs) 0 (j-i)          
           ? lem_toBagBtw_from_right_append xs_l  xs_cr' i j
           ? lem_toBagBtw_from_left_append  xs_c' xs_r   0 (j-i)
           ? lem_toBagBtw_slice xs_cr 0 (j-i) 0 (j-i)
           ? lem_toBagBtw_slice xs i (A.size xs) 0 (j-i)
           ? toProof ( toSlice (A.append xs_l xs_cr') 0 i 
                     ? lem_toSlice_from_left_append xs_l xs_cr' 0 i 
                   === toSlice xs_l 0 i
                   === toSlice (slice xs 0 i) 0 i 
                     ? lem_toSlice_slice xs 0 i 0 i
                   === toSlice xs 0 i
           )
           ? toProof ( toSlice (A.append xs_l xs_cr') j (A.size xs)
                     ? lem_toSlice_from_right_append xs_l  xs_cr' j (A.size xs)
                   === toSlice (A.append xs_c' xs_r) (j-i) (A.size xs - i)
                     ? lem_toSlice_from_right_append xs_c' xs_r (j-i) (A.size xs - i)
                   === toSlice xs_r 0 (A.size xs - j)  
                   === toSlice (slice xs_cr (j-i) (A.size xs - i)) 0 (A.size xs - j)
                     ? lem_toSlice_slice xs_cr (j-i) (A.size xs - i) 0 (A.size xs - j)
                   === toSlice xs_cr (j-i) (A.size xs - i)
                   === toSlice (slice xs i (A.size xs)) (j-i) (A.size xs - i)
                     ? lem_toSlice_slice xs i (A.size xs) (j-i) (A.size xs - i)
                   === toSlice xs j (A.size xs)
           )
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
shuffleBtw :: HasPrimOrd a => Array a -> Int -> Int -> (Array a, Int)
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
          else let (vr, zs'') = A.get2 zs' jr in
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
      {- @ xs'' :: { vs:(Array a) | isPartitionedBtw vs i ip j &&
                                   toSlice xs' 0 i == toSlice vs 0 i && 
                                   toSlice xs' j (A.size xs') == toSlice vs j (A.size xs') &&
                                   A.size xs' == A.size vs &&
                                   toBagBtw xs i j == toBagBtw vs i j } @-}
      xs''       = if ip < j-1 
                   then swap2 xs' ip (j-1) ? lma_swap xs' ip (j-1)
                                           ? lem_bagBtw_swap xs' i ip (j-1) j
                                           ? lem_range_inside_swap xs' ip (j-1)
                                           ? lem_range_outside_swap xs' i ip (j-1) j (get xs' (j-1))
                                           ? lem_toSlice_swap xs' i ip (j-1) j
                   else xs' 
   in (xs'', ip)
--  where

 -- | This belongs in Equivalence.hs but causes a Fixpoint panic if it's there
{-@ lem_toSlice_slice :: xs:_ -> i:Nat  -> { j:Nat  | i <= j && j <= A.size xs }             
                             -> i':Nat -> { j':Nat | i' <= j' && j' <= j - i }
                             -> { pf:_ | toSlice (slice xs i j) i' j' == toSlice xs (i+i') (i+j')} 
                             / [j' - i'] @-}
lem_toSlice_slice :: (HasPrimOrd a, Eq a) => Array a -> Int -> Int -> Int -> Int -> Proof
lem_toSlice_slice xs i j i' j'
    | i' >= j'  = ()
    | otherwise = lem_get_slice xs i j (i'+i)
                ? lem_toSlice_slice xs i j (i'+1) j'


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
rangeUpperBound :: HasPrimOrd a => Array a -> Int -> Int -> a -> Bool
rangeUpperBound xs i j piv = rangeProperty xs i j (belowPivot piv)

{-@ reflect rangeLowerBound @-}
{-@ rangeLowerBound :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i <= j && j <= size xs }
                                    -> a -> Bool @-}
rangeLowerBound :: HasPrimOrd a => Array a -> Int -> Int -> a -> Bool
rangeLowerBound xs i j piv = rangeProperty xs i j (abovePivot piv)

{-@ reflect isPartitionedBtw @-}
{-@ isPartitionedBtw :: xs:(Array a) -> { i:Int | 0 <= i } -> { i_piv:Int | i <= i_piv }
                                     -> { j:Int | i_piv < j && j <= size xs } -> Bool @-}
isPartitionedBtw :: HasPrimOrd a => Array a -> Int -> Int -> Int -> Bool
isPartitionedBtw xs i i_piv j = rangeUpperBound xs i           i_piv   (get xs i_piv)   &&
                                rangeLowerBound xs (i_piv + 1) j       (get xs i_piv)

{-@ lem_range_outside_swap :: xs:(Array a) -> { i:Int | 0 <= i }
                           -> { jl:Int | i <= jl } -> { jr:Int | jl < jr }
                           -> { j:Int  | jr <= j-1 && j <= size xs }
                           -> { piv:a  | rangeUpperBound xs i      jl    piv &&
                                         rangeLowerBound xs (jr+1) j     piv }
                           -> { pf:_ | rangeUpperBound (swap xs jl jr) i      jl    piv &&
                                       rangeLowerBound (swap xs jl jr) (jr+1) j     piv } / [j-i] @-}
lem_range_outside_swap :: HasPrimOrd a => Array a -> Int -> Int -> Int -> Int -> a -> Proof
lem_range_outside_swap xs i jl jr j piv
    | i < jl     = () ? lma_swap_eql xs jl jr i
                      ? lem_range_outside_swap xs (i+1) jl jr j     piv
    | jr+1 < j   = () ? lma_swap_eql xs jl jr (j-1)
                      ? lem_rangeProperty_right xs (jr+1) j (abovePivot piv)
                      ? lem_range_outside_swap xs i     jl jr (j-1) piv
                      ? lem_rangeProperty_build_right (swap xs jl jr) (abovePivot piv) (jr+1) (j-1)
    | otherwise  = ()

{-@ lem_range_inside_swap :: xs:(Array a) -> { jl:Int | 0 <= jl }
                  -> { jr:Int | jl < jr && jr < size xs &&
                                rangeLowerBound xs jl jr (get xs jr) }
                  -> { pf:_ | rangeLowerBound (swap xs jl jr) (jl+1) (jr+1) (get (swap xs jl jr) jl) } @-}
lem_range_inside_swap :: HasPrimOrd a => Array a -> Int -> Int -> Proof
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
{-@ lem_qs_pres_partition_left  :: xs:(Array a) -> { ys:(Array a) | size xs == size ys }
                                -> { i:Int | 0 <= i } -> { i_piv:Int | i <= i_piv }
                                -> { j:Int | i_piv < j && j <= size xs &&
                                             isPartitionedBtw xs i i_piv j &&
                                             toBagBtw xs i i_piv == toBagBtw ys i i_piv &&
                                             toSlice xs i_piv (size xs) == toSlice ys i_piv (size xs) }
                                -> { pf:_  | isPartitionedBtw ys i i_piv j } @-}
lem_qs_pres_partition_left  :: HasPrimOrd a => Array a -> Array a -> Int -> Int -> Int -> Proof
lem_qs_pres_partition_left  xs ys i i_piv j
    = () ? lem_bagBtw_pres_rangeProperty xs ys i i_piv      (belowPivot (get xs i_piv))
         ? lem_bagBtw_pres_rangeProperty xs ys (i_piv+1) (j
         ? lem_equal_slice_narrow     xs ys (i_piv) (i_piv+1) j (size xs)
         ? lem_equal_slice_bag        xs ys         (i_piv+1) j )
                                                            (abovePivot (get xs i_piv))

{-@ lem_qs_pres_partition_right  :: xs:(Array a) -> { ys:(Array a) | size xs == size ys }
                                -> { i:Int | 0 <= i } -> { i_piv:Int | i <= i_piv }
                                -> { j:Int | i_piv < j && j <= size xs &&
                                             isPartitionedBtw xs i i_piv j &&
                                             toBagBtw xs (i_piv+1) j == toBagBtw ys (i_piv+1) j &&
                                             toSlice xs 0 (i_piv+1) == toSlice ys 0 (i_piv+1) }
                                -> { pf:_  | isPartitionedBtw ys i i_piv j } @-}
lem_qs_pres_partition_right :: HasPrimOrd a => Array a -> Array a -> Int -> Int -> Int -> Proof
lem_qs_pres_partition_right xs ys i i_piv j
    = () ? lem_bagBtw_pres_rangeProperty xs ys   i (i_piv
         ? lem_equal_slice_narrow     xs ys 0 i i_piv (i_piv+1)
         ? lem_equal_slice_bag        xs ys   i i_piv )
                                                           (belowPivot (get xs i_piv))
         ? lem_equal_slice_narrow     xs ys 0 i_piv (i_piv+1) (i_piv+1)
         ? lem_bagBtw_pres_rangeProperty xs ys (i_piv+1) j (abovePivot (get xs i_piv))

{-@ lem_sorted_partitions :: xs:(Array a) -> { i:Int | 0 <= i } -> { i_piv:Int | i <= i_piv }
                                          -> { j:Int | i_piv < j && j <= size xs && j - i >= 2 &&
                                                       isSortedBtw xs i         i_piv &&
                                                       isSortedBtw xs (i_piv+1) j &&
                                                       isPartitionedBtw xs i i_piv j }
                                          -> { pf:_ | isSortedBtw xs i j } @-}
lem_sorted_partitions :: HasPrimOrd a => Array a -> Int -> Int -> Int -> Proof
lem_sorted_partitions xs i i_piv j
    | i == i_piv      = ()
    | i_piv + 1 == j  = () ? lem_isSortedBtw_build_right xs i (i_piv
                           ? lem_rangeProperty_right xs i i_piv (belowPivot (get xs i_piv))
                           ? toProof (belowPivot (get xs i_piv) (get xs (i_piv-1))) )
    | otherwise       = () ? lem_isSortedBtw_compose xs i i_piv (j
                           ? lem_rangeProperty_right xs i i_piv (belowPivot (get xs i_piv))
                           ? toProof (belowPivot (get xs i_piv) (get xs (i_piv-1))) )
