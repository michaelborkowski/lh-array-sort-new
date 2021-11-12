{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module QuickSort where

import Language.Haskell.Liquid.ProofCombinators
import Array
-- import Equivalence
import Order

{- @ quickSort :: xs:(Array a) -> { ys:(Array a) | isSorted' ys && toBag xs == toBag ys } @-}
{-@ quickSort :: xs:(Array a) -> { ys:(Array a) | isSorted' ys && size xs == size ys } @-}
quickSort :: Ord a => Array a -> Array a 
quickSort xs = quickSortBtw xs 0 (size xs)

{- @ @-}
{-@ quickSortBtw :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i <= j && j <= size xs }
                                 -> { ys:(Array a) | isSortedBtw ys i j &&
                                                     size xs == size ys } / [j - i] @-}
quickSortBtw :: Ord a => Array a -> Int -> Int -> Array a
quickSortBtw xs i j = if n < 2
                        then xs
                        else let (xs', i_piv) = shuffleBtw xs i j
                                 xs''         = quickSortBtw xs'  i           i_piv
                                 xs'''        = quickSortBtw xs'' (i_piv + 1) j
                              in xs'''        ? lem_sorted_partitions xs''' i i_piv j
  where
    n   = j - i

{- @                              toBagBtw xs 0 i == Map_union (toBagBtw zs 0 jl) 
                                                               (toBagBtw zs (jr+1) (size zs)) @-}  
-- xs ranges from 0..i_piv+1
-- 0 <= i < i_piv  and  0 <= jl < jr <= i_piv
{-@ shuffleBtw :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i + 1 < j && j <= size xs }
                  -> (Array a, Int)<{\ys ip -> isPartitionedBtw ys i ip j &&
                                               i <= ip && ip < j && size ys == size xs }> @-}
shuffleBtw :: Ord a => Array a -> Int -> Int -> (Array a, Int)
shuffleBtw xs i j = let (xs', ip) = goShuffle xs i (j-2) 
                        xs''      = if ip < j-1 
                                      then swap xs' ip (j-1) 
                                         ? lma_swap xs' ip (j-1)
                                         ? lem_rangeLowerBound_right xs' ip (j-1) (get xs' (j-1))
                                         ? lem_range_inside_swap xs' ip (j-1)
                                         ? lem_range_outside_swap xs' i ip (j-1) j (get xs' (j-1))
                                      else xs'
                                  
                     in (xs'', ip)
  where
    piv = get xs (j-1) -- fix xs[j-1] as the pivot     -- toBag xs == toBag ys
    {-@ goShuffle :: { zs:(Array a) | get zs (j-1) == piv && size zs == size xs }
                  -> { jl:Int | i <= jl    &&             rangeUpperBound zs i      jl    piv } 
                  -> { jr:Int | jl <= jr+1 && jr < j-1 && rangeLowerBound zs (jr+1) (j-1) piv }
                  -> (Array a, Int)<{\ws ip -> rangeUpperBound ws i      ip    piv && 
                                               rangeLowerBound ws ip     (j-1) piv &&
                                               size ws == size zs && get ws (j-1) == get zs (j-1) && 
                                               i <= ip && ip < j }> / [jr - jl + 1] @-}
--                  -> (Array a, Int)<{\ws ip -> isPartitionedBtw ws i ip j && 
    --goShuffle :: Ord a => Array a -> Int -> Int -> (Array a, Int)
    goShuffle zs jl jr 
      | jl > jr           = (zs, jl)
                            --(swap zs jl (j-1), jl) 
      | get zs jl <= piv  = goShuffle zs (jl+1) jr
      | get zs jr >  piv  = goShuffle zs jl     (jr-1)
      | otherwise         = let zs' = swap zs jl jr ? lma_swap_eql zs jl jr (j-1)
                                    ? lem_range_outside_swap zs i jl jr j piv
                                    ? lma_swap zs jl jr
                             in goShuffle zs' jl (jr-1)
  
    


{-@ reflect isPartitionedBtw @-}
{-@ isPartitionedBtw :: xs:(Array a) -> { i:Int | 0 <= i } -> { i_piv:Int | i <= i_piv }
                                     -> { j:Int | i_piv < j && j <= size xs } -> Bool @-}
isPartitionedBtw :: Ord a => Array a -> Int -> Int -> Int -> Bool
isPartitionedBtw xs i i_piv j = rangeUpperBound xs i           i_piv     (get xs i_piv) &&
                                rangeLowerBound xs (i_piv + 1) j         (get xs i_piv) 

{-@ reflect rangeUpperBound @-}
{-@ rangeUpperBound :: xs:(Array a) -> { n0:Int | 0 <= n0 } -> { n1:Int | n0 <=n1 && n1 <= size xs }
                                    -> a -> Bool / [n1] @-}
rangeUpperBound :: Ord a => Array a -> Int -> Int -> a -> Bool
rangeUpperBound xs n0 n1 v | n0 >= n1  = True
                           | otherwise = (get xs (n1 - 1) <= v) && rangeUpperBound xs n0 (n1 - 1) v

{-@ reflect rangeLowerBound @-}
{-@ rangeLowerBound :: xs:(Array a) -> { n0:Int | 0 <= n0 } -> { n1:Int | n0 <=n1 && n1 <= size xs }
                                    -> a -> Bool / [n1-n0] @-}
rangeLowerBound :: Ord a => Array a -> Int -> Int -> a -> Bool
rangeLowerBound xs n0 n1 v | n0 >= n1  = True
                           | otherwise = (v < get xs n0) && rangeLowerBound xs (n0+1) n1 v

{-@ lem_rangeUpperBound_left :: xs:(Array a) -> { n0:Int | 0 <= n0 } -> { n1:Int | n0 < n1 && n1 <= size xs }
                             -> { piv:a | rangeUpperBound xs n0 n1 piv }
                             -> { pf:_  | get xs n0 <= piv && rangeUpperBound xs (n0+1) n1 piv } / [n1] @-}
lem_rangeUpperBound_left :: Ord a => Array a -> Int -> Int -> a -> Proof
lem_rangeUpperBound_left xs n0 n1 piv
  | n0 + 1 == n1  = ()
  | otherwise     = () ? lem_rangeUpperBound_left xs n0 (n1-1) piv

{-@ lem_rangeUpperBound_build_left :: xs:(Array a) -> { n0:Int | 0 <= n0 } 
                             -> { n1:Int | n0 < n1 && n1 <= size xs }
                             -> { piv:a | get xs n0 <= piv && rangeUpperBound xs (n0+1) n1 piv }
                             -> { pf:_  |                     rangeUpperBound xs n0     n1 piv } / [n1] @-}
lem_rangeUpperBound_build_left :: Ord a => Array a -> Int -> Int -> a -> Proof
lem_rangeUpperBound_build_left xs n0 n1 piv 
  | n0 + 1 == n1  = ()
  | otherwise     = () ? lem_rangeUpperBound_build_left xs n0 (n1-1) piv

{-@ lem_rangeLowerBound_right :: xs:(Array a) -> { n0:Int | 0 <= n0 } -> { n1:Int | n0 < n1 && n1 <= size xs }
                         -> { piv:a | rangeLowerBound xs n0 n1 piv }
                         -> { pf:_  | get xs (n1-1) > piv && rangeLowerBound xs n0 (n1-1) piv } / [n1-n0] @-}
lem_rangeLowerBound_right :: Ord a => Array a -> Int -> Int -> a -> Proof
lem_rangeLowerBound_right xs n0 n1 piv
  | n0 + 1 == n1  = ()
  | otherwise     = () ? lem_rangeLowerBound_right xs (n0+1) n1 piv

{-@ lem_rangeLowerBound_build_right :: xs:(Array a) -> { n0:Int | 0 <= n0 } 
                         -> { n1:Int | n0 < n1 && n1 <= size xs }
                         -> { piv:a | get xs (n1-1) > piv && rangeLowerBound xs n0 (n1-1) piv }
                         -> { pf:_  |                        rangeLowerBound xs n0     n1 piv } / [n1-n0] @-}
lem_rangeLowerBound_build_right :: Ord a => Array a -> Int -> Int -> a -> Proof
lem_rangeLowerBound_build_right xs n0 n1 piv 
  | n0 + 1 == n1  = ()
  | otherwise     = () ? lem_rangeLowerBound_build_right xs (n0+1) n1 piv

{-@ lem_range_outside_swap :: xs:(Array a) -> { i:Int | 0 <= i } 
                           -> { jl:Int | i <= jl } -> { jr:Int | jl < jr }
                           -> { j:Int  | jr <= j-1 && j <= size xs }
                           -> { piv:a  | rangeUpperBound xs i      jl    piv &&
                                         rangeLowerBound xs (jr+1) (j-1) piv }
                           -> { pf:_ | rangeUpperBound (swap xs jl jr) i      jl    piv &&
                                       rangeLowerBound (swap xs jl jr) (jr+1) (j-1) piv } / [j-i] @-}
lem_range_outside_swap :: Ord a => Array a -> Int -> Int -> Int -> Int -> a -> Proof
lem_range_outside_swap xs i jl jr j piv 
  | i < jl     = () ? lma_swap_eql xs jl jr i
                    ? lem_rangeUpperBound_left xs i jl piv
                    ? lem_rangeUpperBound_build_left (swap xs jl jr) i jl 
                          (piv ? lem_range_outside_swap xs (i+1) jl jr j     piv)
  | jr+1 < j-1 = () ? lma_swap_eql xs jl jr (j-2)
                    ? lem_rangeLowerBound_right xs (jr+1) (j-1) piv
                    ? lem_rangeLowerBound_build_right (swap xs jl jr) (jr+1) (j-1) 
                          (piv ? lem_range_outside_swap xs i     jl jr (j-1) piv)
  | otherwise  = ()

{-@ lem_range_inside_swap :: xs:(Array a) -> { jl:Int | 0 <= jl }
                  -> { jr:Int | jl < jr && jr < size xs && get xs jl > get xs jr &&
                                rangeLowerBound xs jl jr (get xs jr) }
                  -> { pf:_ | rangeLowerBound (swap xs jl jr) (jl+1) (jr+1) (get (swap xs jl jr) jl) } @-}
lem_range_inside_swap :: Ord a => Array a -> Int -> Int -> Proof
lem_range_inside_swap xs jl jr = () ? lma_swap xs jl jr 
                                    ? lem_go_inside_swap (jl+1)
  where
    {-@ lem_go_inside_swap :: { jj:Int | jl < jj && jj <= jr &&
                                         rangeLowerBound xs jj jr (get xs jr) } 
                 -> { pf:_ | rangeLowerBound (swap xs jl jr) jj (jr+1) (get (swap xs jl jr) jl) } / [jr-jj] @-}
    -- lem_range_inside_swap :: Ord a => Array a -> Int -> Int -> Int -> Proof
    lem_go_inside_swap jj 
      | jj < jr    = () ? lma_swap xs jl jr
                        ? lma_swap_eql xs jl jr jj
                        ? lem_go_inside_swap (jj+1) 
      | otherwise  = () ? lma_swap xs jl jr
                          

{-@ lem_sorted_partitions :: xs:(Array a) -> { i:Int | 0 <= i } -> { i_piv:Int | i <= i_piv }
                                          -> { j:Int | i_piv < j && j <= size xs &&
                                                       isSortedBtw xs i         i_piv &&
                                                       isSortedBtw xs (i_piv+1) j &&
                                                       isPartitionedBtw xs i i_piv j } 
                                          -> { pf:_ | isSortedBtw xs i j } @-}
lem_sorted_partitions :: Ord a => Array a -> Int -> Int -> Int -> Proof
lem_sorted_partitions = undefined -- TODO TODO

