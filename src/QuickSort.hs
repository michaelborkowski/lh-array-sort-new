
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorder"  @-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE RankNTypes #-}


module QuickSort where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))

import ProofCombinators
import Array
import ArrayOperations
import Properties.Equivalence
import Properties.Order
import Properties.RangeProperties
import Properties.Partitions

import           Linear.Common
#ifdef MUTABLE_ARRAYS
import qualified Unsafe.Linear as Unsafe
import           Array.Mutable as A
#else
import qualified Linear.Unsafe as Unsafe
import           Array.List as A
#endif
import qualified Array as A

--------------------------------------------------------------------------------

{-@ quickSort :: xs:(Array a) -> { ys:(Array a) | isSorted' ys && A.size xs == A.size ys &&
                                                                  toBag  xs == toBag  ys } @-}
-- quickSort :: (Ord a, Show a) => Array a -> Array a
quickSort :: (HasPrimOrd a, Show a) => Array a -. Array a
quickSort xs =
      let (Ur n, xs1) = A.size2 xs in
      if n == 0 then xs1
      else let (Ur hd, xs2) = A.get2 0 xs1
               tmp = makeArray n hd in
                 A.copy2 0 0 n xs2 tmp ? lem_copy_equal_slice xs2 0 tmp 0 n & \(xs2', cpy0) ->
                   (A.free(xs2'), cpy0) & \((), cpy) ->
                     quickSortBtw 0 n (cpy ? lem_equal_slice_bag   xs2   cpy 0 n)

{-@ quickSort' :: xs:(Array a) -> { ys:(Array a) | isSorted' ys && A.size xs == A.size ys &&
                                                                  toBag  xs == toBag  ys } @-}
quickSort' :: (HasPrimOrd a, Show a) => Array a -. Array a
quickSort' xs =
  let (Ur n, xs1) = A.size2 xs in
  if n == 0 then xs1
  else quickSortBtw 0 n xs1

{-@ quickSortBtw :: { i:Int | 0 <= i } -> { j:Int | i <= j }
                -> { xs:(Array a) | j <= A.size xs } -> { ys:(Array a) | isSortedBtw ys i j && A.size xs == A.size ys &&
                                    toSlice xs 0 i == toSlice ys 0 i &&
                                    toSlice xs j (A.size xs) == toSlice ys j (A.size xs) &&
                                    toBagBtw xs i j == toBagBtw ys i j } / [j - i] @-}
quickSortBtw :: HasPrimOrd a => Int -> Int -> (Array a -. Array a)
quickSortBtw i j xs =
  if j - i < 2
  then xs
  else let (xs', Ur i_piv) = shuffleBtw i j xs
           xs''         = quickSortBtw i i_piv xs'
           xs'''        = quickSortBtw (i_piv + 1) j xs''
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

{-@ shuffleBtw :: { i:Int | 0 <= i } -> j:Int -> { xs:(Array a) | i + 1 < j && j <= A.size xs }
                  -> (Array a, Ur Int)<{\ys ip -> isPartitionedBtw ys i (unur ip) j &&
                                               toSlice xs 0 i == toSlice ys 0 i &&
                                               toSlice xs j (A.size xs) == toSlice ys j (A.size xs) &&
                                               toBagBtw xs i j == toBagBtw ys i j &&
                                               i <= unur ip && unur ip < j && A.size ys == A.size xs }> @-}
shuffleBtw :: forall a. HasPrimOrd a => Int -> Int -> (Array a -. (Array a, Ur Int))
shuffleBtw i j xs = xs & A.get2 (j-1) {- fix (j-1)^th element as the pivot -} & \(Ur piv, xs1) ->
  let
    {-@ goShuffle ::
                      { jl:Int | i <= jl }
                  -> { jr:Int | jl <= jr+1 }
                  -> { zs:(Array a) | get zs (j-1) == piv && A.size zs == A.size xs &&
                                      toBagBtw zs i j == toBagBtw xs i j &&
                                      toSlice xs 0 i == toSlice zs 0 i &&
                                      toSlice xs j (A.size zs) == toSlice zs j (A.size zs)

                                      && rangeUpperBound zs i      jl    piv
                                      && jr < j-1 && rangeLowerBound zs (jr+1) (j-1) piv }
                  -> (Array a, Ur Int)<{\ws ip -> rangeUpperBound ws i (unur ip) piv &&
                                                rangeLowerBound ws (unur ip) (j-1) piv &&
                                                A.size ws == A.size zs &&
                                                get ws (j-1) == get zs (j-1) &&
                                                toBagBtw zs i j == toBagBtw ws i j &&
                                                toBagBtw xs i j == toBagBtw ws i j &&
                                                toSlice zs 0 i == toSlice ws 0 i &&
                                                toSlice zs j (A.size zs) == toSlice ws j (A.size zs) &&
                                                i <= unur ip && unur ip < j }> / [jr - jl + 1] @-}
    -- at return, all of ws[i:ip] <= ws[j-1] and all of ws[ip:j-1] > ws[j-1].
    goShuffle :: HasPrimOrd a => Int -> Int -> (Array a -. (Array a, Ur Int))
    goShuffle jl jr zs =   -- BOTH bounds inclusive here
      if jl > jr
      then (zs, Ur jl)
      else A.get2 jl zs & \(Ur vl, zs') ->
        if vl <= piv
        then goShuffle (jl+1 ? lem_rangeProperty_build_right zs (belowPivot (get zs (j-1)))
                                      i (jl ? toProof (belowPivot (get zs (j-1)) (get zs jl))))
                            jr zs'
        else A.get2 jr zs' & \(Ur vr, zs'') ->
          if vr >  piv
          then goShuffle jl (jr-1) zs''
          else let zs''' = swap2 jl jr zs''
                          ? lem_range_outside_swap zs i jl jr (j-1) piv
                          ? lma_swap        zs   jl jr
                          ? lma_swap_eql zs jl jr (j-1)
                          ? lem_bagBtw_swap zs i jl jr j
                          ? lem_toSlice_swap  zs i jl jr j
                in goShuffle jl (jr-1) zs''' in

    goShuffle i (j-2) xs1 & \(xs', Ur ip) ->  -- BOTH bounds inclusive
  let
    {- @ xs'' :: { vs:(Array a) | isPartitionedBtw vs i ip j &&
                                  toSlice xs' 0 i == toSlice vs 0 i &&
                                  toSlice xs' j (A.size xs') == toSlice vs j (A.size xs') &&
                                  A.size xs' == A.size vs &&
                                  toBagBtw xs i j == toBagBtw vs i j } @-}
    xs''       = if ip < j-1
                  then swap2 ip (j-1) xs' ? lma_swap xs' ip (j-1)
                                          ? lem_bagBtw_swap xs' i ip (j-1) j
                                          ? lem_range_inside_swap xs' ip (j-1)
                                          ? lem_range_outside_swap xs' i ip (j-1) j (get xs' (j-1))
                                          ? lem_toSlice_swap xs' i ip (j-1) j
                   else xs'
  in (xs'', Ur ip)
--  where


  -- Lemmas addressing how recursive calls to quickSortBtw preserve the partition property
{-@ ple lem_qs_pres_partition_left @-}
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

{-@ ple lem_qs_pres_partition_right @-}
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

{-@ ple lem_sorted_partitions @-}
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
