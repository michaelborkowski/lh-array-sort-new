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
  *** QED