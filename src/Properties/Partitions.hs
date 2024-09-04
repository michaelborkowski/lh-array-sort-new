{-@ LIQUID "--reflection"   @-}
{-@ LIQUID "--ple"          @-}
{-@ LIQUID "--short-names"  @-}

{-# LANGUAGE CPP #-}
{- # LANGUAGE Strict #-}
{- # LANGUAGE LinearTypes   #-}

module Partitions where

--import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))

import ProofCombinators
import Array
--import Equivalence
--import Order
import Properties

#ifdef MUTABLE_ARRAYS
import           Array.Mutable
#else
import           Array.List
#endif

--import qualified Data.Primitive.Types as P


-- | The definitions and lemmas below pertain to the partition property w/r/t a pivot element
--      defined in terms of an array slice being bounded from below (strictly) or above (weakly).
--      This is used in Quicksort and its variations.

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