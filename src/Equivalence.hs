{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}


-- {-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

-- assuming the array has distinct values
module Equivalence where

import           Prelude
import           Language.Haskell.Liquid.ProofCombinators
import qualified Data.Set as S
import qualified Language.Haskell.Liquid.Bag as B
import           Array as A
 


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


{-@ lem_toBagBtw_right :: xs:(Array a) -> {i:Int | 0 <= i } -> { j:Int | i < j && j <= A.size xs }
                 -> { pf:_ | toBagBtw xs i j == B.put (A.get xs (j-1)) (toBagBtw xs i (j-1)) } / [j-i] @-}
lem_toBagBtw_right :: Ord a => Array a -> Int -> Int -> Proof
lem_toBagBtw_right xs i j | i + 1 == j  = ()
                          | otherwise   = () ? lem_toBagBtw_right xs (i+1) j

{-@ lem_toBagBtw_compose :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i <= j } 
                         -> { k:Int | j <= k && k <= A.size xs }
                         -> { pf:_  | toBagBtw xs i k == B.union (toBagBtw xs i j) (toBagBtw xs j k) } / [j-i] @-}
lem_toBagBtw_compose :: Ord a => Array a -> Int -> Int -> Int -> Proof
lem_toBagBtw_compose xs i j k | i == j     = ()
                              | otherwise  = () ? lem_toBagBtw_right xs i j
                                                ? lem_toBagBtw_compose xs i (j-1) k

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
lem_bag_swap xs i j | i == j    = () ? lma_swap xs i i
                                     ? lem_toBagBtw_before_swap xs 0 i i j
                                     ? lem_toBagBtw_after_swap  xs i j (j+1) (A.size xs)
                                     ? lem_toBagBtw_compose xs            0 i (A.size xs)
                                     ? lem_toBagBtw_compose (swap xs i i) 0 i (A.size xs)
                    | otherwise = () ? lem_toBagBtw_before_swap xs 0 i i j
                                     ? lem_toBagBtw_swap xs i j  
                                     ? lem_toBagBtw_after_swap  xs i j (j+1) (A.size xs)
                                     ? lem_toBagBtw_compose xs            0 i     (j+1)
                                     ? lem_toBagBtw_compose (swap xs i j) 0 i     (j+1)
                                     ? lem_toBagBtw_compose xs            0 (j+1) (A.size xs)
                                     ? lem_toBagBtw_compose (swap xs i j) 0 (j+1) (A.size xs)

{-@ lem_bagBtw_swap :: xs:(Array a) -> { il:Int | 0 <= il } -> { i:Int | il <= i }
                                 -> { j:Int | i <= j } -> { ir:Int | j < ir && ir <= A.size xs }
                                 -> { pf:_  | toBagBtw (swap xs i j) il ir == toBagBtw xs il ir } @-}
lem_bagBtw_swap :: Ord a => Array a -> Int -> Int -> Int -> Int -> Proof
lem_bagBtw_swap xs il i j ir | i == j    = () ? lma_swap xs i i
                                              ? lem_toBagBtw_before_swap xs il i i j
                                              ? lem_toBagBtw_after_swap  xs i j (j+1) ir
                                              ? lem_toBagBtw_compose xs            il i ir
                                              ? lem_toBagBtw_compose (swap xs i i) il i ir
                             | otherwise = () ? lem_toBagBtw_before_swap xs il i i j
                                              ? lem_toBagBtw_swap xs i j
                                              ? lem_toBagBtw_after_swap  xs i j (j+1) ir
                                              ? lem_toBagBtw_compose xs            il i     (j+1)
                                              ? lem_toBagBtw_compose (swap xs i j) il i     (j+1)
                                              ? lem_toBagBtw_compose xs            il (j+1) ir
                                              ? lem_toBagBtw_compose (swap xs i j) il (j+1) ir

-- {-@ lma_bag_equal :: xs:_ -> x:_ -> n:{v:Nat | v < size xs} -> m:{v:Nat | v <= n} 
--       -> {(toBag (set xs n x) m == toBag xs m)} / [m] @-}
-- lma_bag_equal :: Ord a => Array a -> a -> Int -> Int -> Proof
-- lma_bag_equal xs x n 0 = ()
-- lma_bag_equal xs x n m
--   = toBag (set xs n x) m
--   -- === B.union (B.singleton (A.get (set xs n x) (m-1))) (toBag (set xs n x) (m-1))
--     ? (lma_gns xs n (m-1) x)
--   -- === B.union (B.singleton (A.get xs (m-1))) (toBag (set xs n x) (m-1))
--     ? (lma_bag_equal xs x n (m-1))
--   -- === B.union (B.singleton (A.get xs (m-1))) (toBag xs (m-1))
--   === toBag xs m
--   *** QED

  -- | Equality of Slices
 
{-@ reflect eqlSlice @-}
{-@ eqlSlice :: xs:(Array a) -> { ys:(Array a) | A.size xs == A.size ys } 
                             -> { i:Int | 0 <= i } -> { j:Int | i <= j && j <= A.size xs } -> Bool / [j-i] @-}
eqlSlice :: Eq a => Array a -> Array a -> Int -> Int -> Bool
eqlSlice xs ys i j | i == j     = True
                   | otherwise  = (A.get xs i == A.get ys i) && eqlSlice xs ys (i+1) j

{-@ lem_eqlSlice_right :: xs:(Array a) -> { ys:(Array a) | A.size xs == A.size ys } 
                       -> {i:Int | 0 <= i } -> { j:Int | i < j && j <= A.size xs }
                       -> { pf:_ | eqlSlice xs ys i j <=> 
                              ((A.get xs (j-1) == A.get ys (j-1)) && eqlSlice xs ys i (j-1)) } / [j-i] @-}
lem_eqlSlice_right :: Eq a => Array a -> Array a -> Int -> Int -> Proof
lem_eqlSlice_right xs ys i j | i + 1 == j  = ()
                             | otherwise   = () ? lem_eqlSlice_right xs ys (i+1) j

{-@ lem_eqlSlice_narrow :: xs:(Array a) -> { ys:(Array a) | A.size xs == A.size ys }
                        -> { i:Int | 0 <= i } -> { i':Int | i <= i' } -> { j':Int | i' <= j' } 
                        -> { j:Int | j' <= j && j <= A.size xs && eqlSlice xs ys i j }
                        -> { pf:_  | eqlSlice xs ys i' j' } / [ i' - i + j - j'] @-}
lem_eqlSlice_narrow :: Eq a => Array a -> Array a -> Int -> Int -> Int -> Int -> Proof
lem_eqlSlice_narrow xs ys i i' j' j
     | i < i'     = () ? lem_eqlSlice_narrow xs ys (i+1) i' j' j
     | j' < j     = () ? lem_eqlSlice_narrow xs ys i i' j' (j-1
                       ? lem_eqlSlice_right  xs ys i j)
     | otherwise  = ()

  -- | Set-based equivalence code

{-@ reflect toSet @-}
{-@ toSet :: xs:_ -> n:{v:Nat | v <= A.size xs}
       -> s:_ / [n] @-}
toSet :: Ord a => Array a -> Int -> S.Set a
toSet xs 0 = S.empty
toSet xs n = S.union (S.singleton (A.get xs (n-1))) (toSet xs (n-1))

{-@ reflect equalP @-}
equalP :: Ord a => Array a -> Array a -> Bool
equalP xs ys = (toSet xs (size xs)) == (toSet ys (size ys))

{-@ reflect subArrayR @-}
{-@ subArrayR :: xs:{A.size xs >= 1} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | n <= m && m <= A.size xs} -> c:{v:Nat | v <= m-n} -> ys:{A.size ys == m-n} / [c]@-}
subArrayR :: Array a -> Int -> Int -> Int -> Array a
subArrayR xs n m 0 = make (m-n) (A.get xs 0)  
subArrayR xs n m c = set (subArrayR xs n m (c-1)) (c-1) (A.get xs (n+c-1))

{-@ reflect subArray @-}
{-@ subArray :: xs:{A.size xs >= 1} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | n <= m && m <= A.size xs} -> ys:{A.size ys == m-n}@-}
subArray :: Array a -> Int -> Int -> Array a
subArray xs n m = subArrayR xs n m (m-n)


-- n > m
{-@ lma_set_equal :: xs:_ -> x:_ -> n:{v:Nat | v < A.size xs} -> m:{v:Nat | v <= n} 
      -> {(toSet (set xs n x) m == toSet xs m)} / [m] @-}
lma_set_equal :: Ord a => Array a -> a -> Int -> Int -> Proof
lma_set_equal xs x n 0 = ()
lma_set_equal xs x n m
  = toSet (A.set xs n x) m
  -- === S.union (S.singleton (get (set xs n x) (m-1))) (toSet (set xs n x) (m-1))
    ? (lma_gns xs n (m-1) x)
  -- === S.union (S.singleton (get xs (m-1))) (toSet (set xs n x) (m-1))
    ? (lma_set_equal xs x n (m-1))
  -- === S.union (S.singleton (get xs (m-1))) (toSet xs (m-1))
  === toSet xs m
  *** QED
