{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-# LANGUAGE GADTs #-}

module Equivalence where

import           Prelude
import           Language.Haskell.Liquid.ProofCombinators
import qualified Data.Set as S
import qualified Language.Haskell.Liquid.Bag as B
import           Array as A
import           Order

  -- | Key Lemma about Bags in general

{-@ lem_bag_getput :: v:a -> b:(B.Bag a) -> { pf:_ | B.get v (B.put v b) > 0 } @-}
lem_bag_getput :: Ord a => a -> B.Bag a -> Proof
lem_bag_getput v b = toProof ( B.get v (B.put v b) === 1 + B.get v b ) 

  -- | Reflected operation to represent the elements in an array as a multiset

{-@ reflect toBag @-}
{-@ toBag :: xs:(Array a) -> s:(B.Bag a) @-}
toBag :: Ord a => Array a -> B.Bag a
toBag xs = toBagBtw xs 0 (size xs)

{-@ reflect toBagBtw @-}
{-@ toBagBtw :: xs:(Array a) -> {i:Int | 0 <= i } -> { j:Int | i <= j && j <= A.size xs }
                             -> s:(B.Bag a) / [j - i] @-} 
toBagBtw :: Ord a => Array a -> Int -> Int -> B.Bag a
toBagBtw xs i j | i == j     = B.empty
                | otherwise  = B.put (A.get xs i) (toBagBtw xs (i+1) j)

  -- | Basic properties of toBagBtw

{-@ lem_toBagBtw_right :: xs:(Array a) -> {i:Int | 0 <= i } -> { j:Int | i < j && j <= A.size xs }
                 -> { pf:_ | toBagBtw xs i j == B.put (A.get xs (j-1)) (toBagBtw xs i (j-1)) } / [j-i] @-}
lem_toBagBtw_right :: Ord a => Array a -> Int -> Int -> Proof
lem_toBagBtw_right xs i j | i + 1 == j  = ()
                          | otherwise   = () ? lem_toBagBtw_right xs (i+1) j

{-@ lem_toBagBtw_compose' :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i <= j } 
                         -> { k:Int | j <= k && k <= A.size xs }
                         -> { pf:_  | toBagBtw xs i k == B.union (toBagBtw xs i j) (toBagBtw xs j k) } / [j-i] @-}
lem_toBagBtw_compose' :: Ord a => Array a -> Int -> Int -> Int -> Proof
lem_toBagBtw_compose' xs i j k | i == j     = ()
                               | otherwise  = () ? lem_toBagBtw_right xs i j
                                                 ? lem_toBagBtw_compose' xs i (j-1) k

{-@ lem_toBagBtw_compose :: xs:(Array a) -> { ys:(Array a) | A.size xs == A.size ys }
                         -> { i:Int | 0 <= i } -> { j:Int | i <= j && toBagBtw xs i j == toBagBtw ys i j } 
                         -> { k:Int | j <= k && k <= A.size xs && toBagBtw xs j k == toBagBtw ys j k }
                         -> { pf:_  | toBagBtw xs i k == toBagBtw ys i k } / [j-i] @-}
lem_toBagBtw_compose :: Ord a => Array a -> Array a -> Int -> Int -> Int -> Proof
lem_toBagBtw_compose xs ys i j k = () ? lem_toBagBtw_compose' xs i j k
                                      ? lem_toBagBtw_compose' ys i j k

  -- An element v \in xs[i:j] only if exists k. i <= k < j and v = xs[k] 

{-@ lem_inBagBtw_index :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int  | i < j && j <= A.size xs }
                                       -> { v:a   | B.get v (toBagBtw xs i j) > 0 } 
                                       -> { k:Int | i <= k && k < j && v == A.get xs k } / [j - i]  @-}
lem_inBagBtw_index :: Ord a => Array a -> Int -> Int -> a -> Int
lem_inBagBtw_index xs i j v | A.get xs i == v   = i
                            | otherwise         = lem_inBagBtw_index xs (i+1) j v

{-@ lem_index_inBagBtw :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int  | i < j && j <= A.size xs }
                                       -> { k:Int | i <= k && k < j }
                                       -> { pf:_  | B.get (A.get xs k) (toBagBtw xs i j) >= 1 } / [j - i] @-}
lem_index_inBagBtw :: Ord a => Array a -> Int -> Int -> Int -> Proof
lem_index_inBagBtw xs i j k | i == k    = () ? lem_bag_getput (A.get xs i) (toBagBtw xs (i+1) j)
                            | otherwise = () ? lem_index_inBagBtw xs (i+1) j k

  -- | Some ground truth: equality of toBagBtw means permuted array elements
  
{-@ lem_equal_toBagBtw_index :: xs:(Array a) -> { ys:(Array a) | A.size xs == A.size ys } -> { i:Int  | 0 <= i } 
                             -> { j:Int  | i < j   && j <= A.size xs && toBagBtw xs i j == toBagBtw ys i j }
                             -> { k:Int  | i <= k  && k < j }
                             -> { k':Int | i <= k' && k' < j && A.get xs k == A.get ys k' } @-}
lem_equal_toBagBtw_index :: Ord a => Array a -> Array a -> Int -> Int -> Int -> Int
lem_equal_toBagBtw_index xs ys i j k = lem_inBagBtw_index ys i j (A.get xs k
                                     ? lem_index_inBagBtw xs i j k)

  -- | Lemmas establishing that toBag/toBagBtw is preserved under swaps

{-@ lem_toBagBtw_inside_swap :: xs:(Array a) -> { i:Int | 0 <= i } -> { i':Int | i < i' }
                             -> { j':Int | i' <= j'} -> { j:Int | j' <= j && j < A.size xs }
                             -> { pf:_ | toBagBtw (swap xs i j) i' j' == toBagBtw xs i' j' } / [j'-i'] @-}
lem_toBagBtw_inside_swap :: Ord a => Array a -> Int -> Int -> Int -> Int -> Proof
lem_toBagBtw_inside_swap xs i i' j' j | i' == j'  = ()
                                      | otherwise = () ? lma_swap_eql xs i j i'
                                                       ? lem_toBagBtw_inside_swap xs i (i'+1) j' j

{-@ lem_toBagBtw_before_swap :: xs:(Array a) -> { i':Int | 0 <= i' } -> { j':Int | i' <= j' }
                             -> { i:Int |  j' <= i } -> { j:Int | i <= j && j < A.size xs }
                             -> { pf:_ | toBagBtw (swap xs i j) i' j' == toBagBtw xs i' j' } / [j'-i'] @-}
lem_toBagBtw_before_swap :: Ord a => Array a -> Int -> Int -> Int -> Int -> Proof
lem_toBagBtw_before_swap xs i' j' i j | i' == j'  = ()
                                      | otherwise = () ? lma_swap_eql xs i j i'
                                                       ? lem_toBagBtw_before_swap xs (i'+1) j' i j

{-@ lem_toBagBtw_after_swap :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i <= j }
                             -> { i':Int | j < i' } -> { j':Int | i' <= j' && j' <= A.size xs}
                             -> { pf:_ | toBagBtw (swap xs i j) i' j' == toBagBtw xs i' j' } / [j'-i'] @-}
lem_toBagBtw_after_swap :: Ord a => Array a -> Int -> Int -> Int -> Int -> Proof
lem_toBagBtw_after_swap xs i j i' j' | i' == j'  = ()
                                     | otherwise = () ? lma_swap_eql xs i j i'
                                                      ? lem_toBagBtw_after_swap xs i j (i'+1) j'

{-@ lem_toBagBtw_swap :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i <= j && j < A.size xs }
                             -> { pf:_ | toBagBtw (swap xs i j) i (j+1) == toBagBtw xs i (j+1) } @-}
lem_toBagBtw_swap :: Ord a => Array a -> Int -> Int -> Proof
lem_toBagBtw_swap xs i j | i == j    = () ? lma_swap xs i i
                         | otherwise = () ? lem_toBagBtw_inside_swap xs i (i+1) j j
                                          ? lma_swap xs i j
                                          ? lem_toBagBtw_right xs i (j+1)
                                          ? lem_toBagBtw_right (swap xs i j) i (j+1)


{-@ lem_bag_swap :: xs:(Array a) -> { i:Int | 0 <= i } 
                                 -> { j:Int | i <= j && j < A.size xs }
                                 -> { pf:_  | toBag (swap xs i j) == toBag xs } @-}
lem_bag_swap :: Ord a => Array a -> Int -> Int -> Proof
lem_bag_swap xs i j = () ? lem_bagBtw_swap xs 0 i j (size xs) 
                         ? toProof (size (swap xs i j) === size xs)

{-@ lem_bagBtw_swap :: xs:(Array a) -> { il:Int | 0 <= il } -> { i:Int | il <= i }
                                 -> { j:Int | i <= j } -> { ir:Int | j < ir && ir <= A.size xs }
                                 -> { pf:_  | toBagBtw (swap xs i j) il ir == toBagBtw xs il ir } @-}
lem_bagBtw_swap :: Ord a => Array a -> Int -> Int -> Int -> Int -> Proof
lem_bagBtw_swap xs il i j ir | i == j    = () ? lma_swap xs i i
                                              ? lem_toBagBtw_before_swap xs il i i j
                                              ? lem_toBagBtw_after_swap  xs i j (j+1) ir
                                              ? lem_toBagBtw_compose xs (swap xs i i) il i ir
                             | otherwise = () ? lem_toBagBtw_before_swap xs il i i j
                                              ? lem_toBagBtw_swap xs i j
                                              ? lem_toBagBtw_after_swap  xs i j (j+1) ir
                                              ? lem_toBagBtw_compose xs (swap xs i j) il i     (j+1)
                                              ? lem_toBagBtw_compose xs (swap xs i j) il (j+1) ir

  -- | Equality of Slices

{-@ reflect toSlice @-}
{-@ toSlice :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i <= j && j <= A.size xs } 
                            -> [a] / [j-i] @-}
toSlice :: Eq a => Array a -> Int -> Int -> [a]
toSlice xs i j | i == j     = []
               | otherwise  = (A.get xs i) : (toSlice xs (i+1) j)

{-@ reflect appendList @-}
appendList :: Eq a => [a] -> [a] -> [a]
appendList []     ys = ys
appendList (x:xs) ys = x : (appendList xs ys)

{-@ lem_appendList_injective :: xs:[a] -> y:a ->  xs':[a] 
                         -> { y':a | appendList xs [y] == appendList xs' [y'] } 
                         -> { pf:_    | xs == xs' } @-}
lem_appendList_injective :: Eq a => [a] -> a -> [a] -> a -> Proof
lem_appendList_injective []     y []       y' = ()
lem_appendList_injective (x:xs) y (x':xs') y' = () ? lem_appendList_injective xs y xs' y'

{-@ lem_toSlice_right :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i < j && j <= A.size xs }
                      -> { pf:_ | toSlice xs i j == appendList (toSlice xs i (j-1)) [A.get xs (j-1)] } / [j - i] @-}
lem_toSlice_right :: Ord a => Array a -> Int -> Int -> Proof
lem_toSlice_right xs i j | i + 1 == j  = ()
                         | otherwise   = () ? lem_toSlice_right xs (i+1) j

{-@ lem_equal_slice_narrow :: xs:(Array a) -> { ys:(Array a) | A.size xs == A.size ys }
                        -> { i:Int | 0 <= i } -> { i':Int | i <= i' } -> { j':Int | i' <= j' }
                        -> { j:Int | j' <= j && j <= A.size xs && toSlice xs i j == toSlice ys i j }
                        -> { pf:_  | toSlice xs i' j' == toSlice ys i' j' } / [ i' - i + j - j'] @-}
lem_equal_slice_narrow :: Ord a => Array a -> Array a -> Int -> Int -> Int -> Int -> Proof
lem_equal_slice_narrow xs ys i i' j' j
    | i < i'      = () ? lem_equal_slice_narrow xs ys (i+1) i' j' j
    | j' < j      = () ? lem_equal_slice_narrow xs ys i i' j' (j-1
                       ? lem_toSlice_right xs i j
                       ? lem_toSlice_right ys i j
                       ? lem_appendList_injective (toSlice xs i (j-1)) (A.get xs (j-1)) 
                                              (toSlice ys i (j-1)) (A.get ys (j-1)))
    | otherwise   = ()
                            
{-@ lem_equal_slice_bag ::  xs:(Array a) -> { ys:(Array a) | A.size xs == A.size ys }
                        -> { i:Int | 0 <= i } 
                        -> { j:Int | i <= j && j <= A.size xs && toSlice xs i j == toSlice ys i j }
                        -> { pf:_  | toBagBtw xs i j == toBagBtw ys i j } / [j - i] @-}
lem_equal_slice_bag :: Ord a => Array a -> Array a -> Int -> Int -> Proof
lem_equal_slice_bag xs ys i j | i == j    = ()
                              | otherwise = () ? lem_equal_slice_bag xs ys (i+1) j
 
{-@ lem_toSlice_swap :: xs:(Array a) -> { il:Int | 0 <= il } -> { i:Int | il <= i }
        -> { j:Int | i <= j } -> { ir:Int | j < ir && ir <= A.size xs }
        -> { pf:_  | toSlice xs 0 il == toSlice (swap xs i j) 0   il &&
                     toSlice xs ir (A.size xs) == toSlice (swap xs i j) ir (A.size xs) } / [il+(A.size xs)-ir] @-}
lem_toSlice_swap :: Ord a => Array a -> Int -> Int -> Int -> Int -> Proof
lem_toSlice_swap xs il i j ir
    | 0 < il           = () ? lem_toSlice_swap  xs (il-1) i j ir
                            ? lma_swap_eql      xs        i j (il-1)
                            ? lem_toSlice_right xs            0 il
                            ? lem_toSlice_right (swap xs i j) 0 il
    | ir < (A.size xs) = () ? lem_toSlice_swap  xs il     i j (ir+1)
                            ? lma_swap_eql      xs        i j ir
    | otherwise        = ()

 -- | sortedness is preserved under eqlSlice (because nothing changed in the slice!)
{-@ lem_equal_slice_sorted :: xs:(Array a) -> { ys:(Array a) | A.size xs == A.size ys }
                           -> { i:Int  | 0 <= i } -> { i':Int | i <= i' } 
                           -> { j':Int | i' <= j' && isSortedBtw xs i' j' }
                           -> { j:Int  | j' <= j  && j <= A.size xs && toSlice xs i j == toSlice ys i j }
                           -> { pf:_   | isSortedBtw ys i' j' } / [j' - i'] @-}
lem_equal_slice_sorted :: Ord a => Array a -> Array a -> Int -> Int -> Int -> Int -> Proof
lem_equal_slice_sorted xs ys i i' j' j 
    | i' + 1 >= j'   = ()
    | otherwise      = () ? lem_equal_slice_narrow xs ys i i' (i'+2) j
                          ? lem_equal_slice_sorted xs ys i (i'+1) j' j

  -- | Elvis's bags 

{-@ reflect toBagLeft @-}
{-@ toBagLeft :: xs:(Array a) -> n:{v:Nat | v <= A.size xs}
                             -> s:(B.Bag a) / [n] @-} 
toBagLeft :: Ord a => Array a -> Int -> B.Bag a
toBagLeft xs 0 = B.empty
toBagLeft xs n = B.put (A.get xs (n-1)) (toBagLeft xs (n-1))

{-@ reflect toBagEqual @-}
toBagEqual :: Ord a => Array a -> Array a -> Bool
toBagEqual xs ys = (toBagLeft xs (size xs)) == (toBagLeft ys (size ys))

-- n > m
{-@ lma_set_equal :: xs:_ -> x:_ -> n:{v:Nat | v < A.size xs} -> m:{v:Nat | v <= n} 
      -> {(toBagLeft (set xs n x) m == toBagLeft xs m)} / [m] @-}
lma_set_equal :: Ord a => Array a -> a -> Int -> Int -> Proof
lma_set_equal xs x n 0 = ()
lma_set_equal xs x n m
  = toBagLeft (A.set xs n x) m
  -- === S.union (S.singleton (get (set xs n x) (m-1))) (toSet (set xs n x) (m-1))
    ? (lma_gns xs n (m-1) x)
  -- === S.union (S.singleton (get xs (m-1))) (toSet (set xs n x) (m-1))
    ? (lma_set_equal xs x n (m-1))
  -- === S.union (S.singleton (get xs (m-1))) (toSet xs (m-1))
  === toBagLeft xs m
  *** QED-- {-@ reflect tri @-}
