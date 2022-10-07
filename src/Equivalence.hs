{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}

module Equivalence where

import           Prelude
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import qualified Data.Set as S
import qualified Language.Haskell.Liquid.Bag as B
import           Array 
import           Order

#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
#else
import           Array.List as A
#endif

  -- | Key Lemma about Bags in general

{-@ lem_bag_getput :: v:a -> b:(B.Bag a) -> { pf:_ | B.get v (B.put v b) > 0 } @-}
lem_bag_getput :: Ord a => a -> B.Bag a -> Proof
lem_bag_getput v b = toProof ( B.get v (B.put v b) === 1 + B.get v b ) 

{-@ lem_bag_union :: v:a -> b:(B.Bag a) -> b':(B.Bag a)
                         -> { pf:_ | B.put v (B.union b b') == B.union (B.put v b) b' } @-}
lem_bag_union :: Ord a => a -> B.Bag a -> B.Bag a -> Proof
lem_bag_union v b b' = ()

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

  -- | Lemmas connecting toBag/toBagBtw to slice/append

{-@ lem_toBagBtw_slice :: xs:_ -> l:Nat  -> { r:Nat | l <= r && r <= A.size xs }
                               -> i:Nat  -> { j:Nat | i <= j && j <= r-l }
                               -> { pf:_ | toBagBtw (A.slice xs l r) i j == toBagBtw xs (l+i) (l+j) } / [j-i] @-}
lem_toBagBtw_slice :: Ord a => Array a -> Int -> Int -> Int -> Int -> Proof
lem_toBagBtw_slice xs l r i j | i == j    = ()
                              | i <  j 
                                   = toProof ( toBagBtw (A.slice xs l r) i j 
                                           === B.put (A.get (A.slice xs l r) i) (toBagBtw (A.slice xs l r) (i+1) j)
                                             ? lem_get_slice xs l r (i+l)
                                           === B.put (A.get xs (i+l)) (toBagBtw (A.slice xs l r) (i+1) j)
                                             ? lem_toBagBtw_slice xs l r (i+1) j
                                           === B.put (A.get xs (i+l)) (toBagBtw xs (l+i+1) (l+j))
                                           === toBagBtw xs (l+i) (l+j) )

{-@ lem_toBag_slice :: xs:_ -> { l:Nat | l <= A.size xs } 
                            -> { r:Nat | l <= r && r <= A.size xs }
                            -> { pf:_ | toBag (A.slice xs l r) == toBagBtw xs l r } / [ r - l ] @-}
lem_toBag_slice :: Ord a => Array a -> Int -> Int -> Proof
lem_toBag_slice xs i j = lem_toBagBtw_slice xs i j 0 (j-i)

{-@ lem_toBag_splitMid :: xs:_ 
      -> { pf:_ | toBag xs == B.union (toBag (fst (splitMid xs))) (toBag (snd (splitMid xs))) } @-}
lem_toBag_splitMid :: Ord a => Array a -> Proof
lem_toBag_splitMid xs = () ? lem_toBag_slice       xs 0 m
                           ? lem_toBag_slice       xs m n
                           ? lem_toBagBtw_compose' xs 0 m n
  where
    n = A.size xs
    m = n `div` 2

{-@ lem_toBag_splitAt :: i:Nat -> { xs:_ | i <= A.size xs }
      -> { pf:_ | toBag xs == B.union (toBag (fst (A.splitAt i xs))) (toBag (snd (A.splitAt i xs))) } @-}
lem_toBag_splitAt :: Ord a => Int -> Array a -> Proof
lem_toBag_splitAt i xs = () ? lem_toBag_slice       xs 0 i
                            ? lem_toBag_slice       xs   i (A.size xs)
                            ? lem_toBagBtw_compose' xs 0 i (A.size xs)

{-@ lem_toBag_append :: xs:_ -> { ys:_ | token xs == token ys && right xs == left ys }
                             -> { pf:_ | toBag (A.append xs ys) == B.union (toBag xs) (toBag ys) } @-}
lem_toBag_append :: Ord a => Array a -> Array a -> Proof
lem_toBag_append xs ys 
    = () ? lem_toBagBtw_compose' (A.append xs ys) 0 (A.size xs) (A.size xs + A.size ys)
         ? lem_toBag_slice       (A.append xs ys) 0 (A.size xs)
         ? lem_toBag_slice       (A.append xs ys)   (A.size xs) (A.size xs + A.size ys)
         ? lem_slice_append    xs ys 
                          


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

  -- | Equality of Slices (specifically for the QuickSort algo)

{-@ reflect toSlice @-}
{-@ toSlice :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i <= j && j <= A.size xs } 
                            -> [a] / [j-i] @-}
toSlice :: Eq a => Array a -> Int -> Int -> [a]
toSlice xs i j | i == j     = []
               | otherwise  = (A.get xs i) : (toSlice xs (i+1) j)

{-@ lem_get_toSlice :: xs:_ -> { ys:(Array a) | A.size xs == A.size ys } 
                            -> l:Nat -> { i:Nat | l <= i } 
                            -> { r:Nat | i < r && r <= A.size xs && 
                                                  toSlice xs l r == toSlice ys l r }
                            -> { pf:_ | A.get xs i == A.get ys i } / [r - l] @-}
lem_get_toSlice :: Eq a => Array a -> Array a -> Int -> Int -> Int -> Proof
lem_get_toSlice xs ys l i r | l == i     = ()
                            | otherwise  = () ? lem_get_toSlice xs ys (l+1) i r

{-@ lem_toSlice_set_left :: xs:_ -> { i:Nat | i < A.size xs } -> v:a 
                                 -> l:Nat -> { r:Nat | l <= r && r <= i }
                                 -> { pf:_  | toSlice (A.set xs i v) l r == toSlice xs l r } / [r-l] @-}
lem_toSlice_set_left :: Eq a => Array a -> Int -> a -> Int -> Int -> Proof
lem_toSlice_set_left xs i v l r | l == r    = ()
                                | otherwise = () ? lem_toSlice_set_left xs i v (l+1) r
                                                 ? lma_gns            xs i l v

{-@ lem_toSlice_set_right :: xs:_ -> { i:Nat | i < A.size xs } -> v:a 
                                  -> { l:Nat | i < l } -> { r:Nat | l <= r && r <= A.size xs }
                                  -> { pf:_  | toSlice (A.set xs i v) l r == toSlice xs l r } / [r-l] @-}
lem_toSlice_set_right :: Eq a => Array a -> Int -> a -> Int -> Int -> Proof
lem_toSlice_set_right xs i v l r | l == r    = ()
                                 | otherwise = () ? lem_toSlice_set_right xs i v (l+1) r
                                                  ? lma_gns             xs i l v

{-@ lem_toSlice_set :: xs:_ -> { i:Nat | i < A.size xs } -> v:a 
                            -> { pf:_  | toSlice (A.set xs i v) 0 i == toSlice xs 0 i &&
                                         toSlice (A.set xs i v) (i+1) (A.size xs) ==
                                         toSlice xs (i+1) (A.size xs) } @-}
lem_toSlice_set :: Eq a => Array a -> Int -> a -> Proof
lem_toSlice_set xs i v = () ? lem_toSlice_set_left  xs i v 0 i
                            ? lem_toSlice_set_right xs i v (i+1) (A.size xs)

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
lem_toSlice_right :: Eq a => Array a -> Int -> Int -> Proof
lem_toSlice_right xs i j | i + 1 == j  = ()
                         | otherwise   = () ? lem_toSlice_right xs (i+1) j

-- same relative indices in each array, arbitrary narrowing
{-@ lem_equal_slice_narrow :: xs:(Array a) -> { ys:(Array a) | A.size xs == A.size ys }
                        -> { i:Int | 0 <= i } -> { i':Int | i <= i' } -> { j':Int | i' <= j' }
                        -> { j:Int | j' <= j && j <= A.size xs && toSlice xs i j == toSlice ys i j }
                        -> { pf:_  | toSlice xs i' j' == toSlice ys i' j' } / [ i' - i + j - j'] @-}
lem_equal_slice_narrow :: Eq a => Array a -> Array a -> Int -> Int -> Int -> Int -> Proof
lem_equal_slice_narrow xs ys i i' j' j
    | i < i'      = () ? lem_equal_slice_narrow xs ys (i+1) i' j' j
    | j' < j      = () ? lem_equal_slice_narrow xs ys i i' j' (j-1
                       ? lem_toSlice_right xs i j
                       ? lem_toSlice_right ys i j
                       ? lem_appendList_injective (toSlice xs i (j-1)) (A.get xs (j-1)) 
                                              (toSlice ys i (j-1)) (A.get ys (j-1)))
    | otherwise   = ()
                            
-- different relative indices, narrowing by one from the left
{-@ lem_equal_slice_narrow' :: xs:(Array a) -> ys:(Array a) 
                    -> i:Nat  -> { j:Int  | i < j && j <= A.size xs }
                    -> i':Nat -> { j':Int | i' < j' && j' <= A.size ys && j - i == j' - i' &&
                                            toSlice xs i j == toSlice ys i' j' }
                    -> { pf:_  | toSlice xs (i+1) j == toSlice ys (i'+1) j' } / [ i' - i + j - j'] @-}
lem_equal_slice_narrow' :: Eq a => Array a -> Array a -> Int -> Int -> Int -> Int -> Proof
lem_equal_slice_narrow' xs ys i j i' j' = ()
{-    | i < i'      = () ? lem_equal_slice_narrow xs ys (i+1) i' j' j
    | j' < j      = () ? lem_equal_slice_narrow xs ys i i' j' (j-1
                       ? lem_toSlice_right xs i j
                       ? lem_toSlice_right ys i j
                       ? lem_appendList_injective (toSlice xs i (j-1)) (A.get xs (j-1)) 
                                              (toSlice ys i (j-1)) (A.get ys (j-1)))
    | otherwise   = () -}
                            
{-@ lem_equal_slice_bag ::  xs:(Array a) -> { ys:(Array a) | A.size xs == A.size ys }
                        -> { i:Int | 0 <= i } 
                        -> { j:Int | i <= j && j <= A.size xs && toSlice xs i j == toSlice ys i j }
                        -> { pf:_  | toBagBtw xs i j == toBagBtw ys i j } / [j - i] @-}
lem_equal_slice_bag :: Ord a => Array a -> Array a -> Int -> Int -> Proof
lem_equal_slice_bag xs ys i j | i == j    = ()
                              | otherwise = () ? lem_equal_slice_bag xs ys (i+1) j

{-@ lem_equal_slice_bag' :: xs:(Array a) -> ys:(Array a) 
                    -> { i:Int  | 0 <= i }  
                    -> { j:Int  | i <= j && j <= A.size xs }
                    -> { i':Int | 0 <= i' } 
                    -> { j':Int | i' <= j' && j' <= A.size ys && j - i == j' - i' &&
                                  toSlice  xs i j == toSlice  ys i' j' }
                    -> { pf:_   | toBagBtw xs i j == toBagBtw ys i' j' } / [j' - i'] @-}
lem_equal_slice_bag' :: Ord a => Array a -> Array a -> Int -> Int -> Int -> Int -> Proof
lem_equal_slice_bag' xs ys i j i' j'  
    | i'  >= j'   = ()
    | otherwise   = () ? lem_equal_slice_narrow' xs ys i j i' j'
                       ? lem_equal_slice_bag' xs ys (i+1) j (i'+1) j'                              
 
{-@ lem_toSlice_swap :: xs:(Array a) -> { il:Int | 0 <= il } -> { i:Int | il <= i }
        -> { j:Int | i <= j } -> { ir:Int | j < ir && ir <= A.size xs }
        -> { pf:_  | toSlice xs 0 il == toSlice (swap xs i j) 0   il &&
                     toSlice xs ir (A.size xs) == toSlice (swap xs i j) ir (A.size xs) } / [il+(A.size xs)-ir] @-}
lem_toSlice_swap :: Eq a => Array a -> Int -> Int -> Int -> Int -> Proof
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

{-@ lem_equal_slice_sorted' :: xs:(Array a) -> ys:(Array a) 
                    -> { i:Int  | 0 <= i }  
                    -> { j:Int  | i <= j && j <= A.size xs && isSortedBtw xs i j }
                    -> { i':Int | 0 <= i' } 
                    -> { j':Int | i' <= j' && j' <= A.size ys && j - i == j' - i' &&
                                  toSlice xs i j == toSlice ys i' j' }
                    -> { pf:_   | isSortedBtw ys i' j' } / [j' - i'] @-}
lem_equal_slice_sorted' :: Ord a => Array a -> Array a -> Int -> Int -> Int -> Int -> Proof
lem_equal_slice_sorted' xs ys i j i' j'  
    | i' + 1 >= j'   = ()
    | otherwise      = () ? lem_equal_slice_narrow' xs ys i j i' j'
                          ? lem_equal_slice_sorted' xs ys (i+1) j (i'+1) j'

{-@ lem_copy_equal_slice :: xs:_ -> { xi:Nat | xi <= A.size xs } -> ys:_
        -> { yi:Nat | yi <= A.size ys }
        -> { n:Nat  | xi + n <= A.size xs && yi + n <= A.size ys }
        -> { zs:_   | toSlice (copy xs xi ys yi n) 0 yi == toSlice ys 0 yi && 
                      toSlice (copy xs xi ys yi n) yi (yi+n) == toSlice xs xi (xi+n) &&
                      toSlice (copy xs xi ys yi n) (yi+n) (A.size ys) 
                                     == toSlice ys (yi+n) (A.size ys) } / [n] @-} {- -}
lem_copy_equal_slice :: Eq a => Array a -> Int -> Array a -> Int -> Int -> Proof
lem_copy_equal_slice xs xi ys yi 0 = ()
lem_copy_equal_slice xs xi ys yi n 
    = () ? lem_copy_equal_slice xs xi ys yi (n-1)
         ? lem_toSlice_set_left  (copy xs xi ys yi (n-1)) (yi+n-1) (get xs (xi+n-1)) 0 yi
         ? lem_toSlice_set_right (copy xs xi ys yi (n-1)) (yi+n-1) (get xs (xi+n-1)) (yi+n) (A.size ys)
           {- IH gives us: toSlice (copy xs xi ys yi (n-1)) yi (yi+n-1) == toSlice xs xi (xi+n-1) -}
           {-   to show LHS == toSlice (copy xs xi ys yi n) yi (yi+n-1) : -}
         ? lem_toSlice_set_left  (copy xs xi ys yi (n-1)) (yi+n-1) (get xs (xi+n-1)) yi (yi+n-1)
           {-   to show get (copy xs xi ys yi n) (yi+n) = get xs (xi+n) : -}
         ? lem_toSlice_right xs xi (xi+n)
         ? lem_toSlice_right (copy xs xi ys yi n) yi (yi+n)   
         ? lma_gs (copy xs xi ys yi (n-1)) (yi + n - 1) (get xs (xi + n - 1))
    


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


{-@ lma_toBag_toBagLeft :: xs:_ -> n:{ Nat | n <= A.size xs}
      -> { toBagLeft xs n == toBagBtw xs 0 n } / [n] @-}
lma_toBag_toBagLeft :: Ord a => Array a -> Int -> Proof
lma_toBag_toBagLeft xs 0 = ()
lma_toBag_toBagLeft xs n
  = toBagBtw xs 0 n
    ? (lem_toBagBtw_right xs 0 n)
  === B.put (A.get xs (n-1)) (toBagBtw xs 0 (n-1))
    ? (lma_toBag_toBagLeft xs (n-1))
  === B.put (A.get xs (n-1)) (toBagLeft xs (n-1))
  === toBagLeft xs n
  *** QED


-- {-@ lma_toBag_toBagEqual :: xs:_ -> ys:{ A.size xs == A.size ys } 
--       -> { toBagEqual xs ys <=> (toBag xs == toBag ys)} @-}
-- lma_toBag_toBagEqual :: Ord a => Array a -> Array a -> Proof
-- lma_toBag_toBagEqual xs ys 
--   = toBagEqual xs ys
--   === (toBagLeft xs (size xs)) == (toBagLeft ys (size ys))
--   === 
--   === (toBagBtw xs 0 (size xs)) == (toBagBtw ys 0 (size ys))
