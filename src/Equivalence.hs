{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}


-- {-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

-- assuming the array has distinct values
module Equivalence where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified Data.Set as S
import           Array


{-@ reflect toSet @-}
{-@ toSet :: xs:_ -> n:{v:Nat | v <= size xs}
       -> s:_ / [n] @-}
toSet :: Ord a => Array a -> Int -> S.Set a
toSet xs 0 = S.empty
toSet xs n = S.union (S.singleton (get xs (n-1))) (toSet xs (n-1))

{-@ reflect equalP @-}
equalP :: Ord a => Array a -> Array a -> Bool
equalP xs ys = (toSet xs (size xs)) == (toSet ys (size ys))

{-@ reflect subArrayR @-}
{-@ subArrayR :: xs:{size xs >= 1} -> n:{v:Nat | v <= size xs} -> m:{v:Nat | n <= m && m <= size xs} -> c:{v:Nat | v <= m-n} -> ys:{size ys == m-n} / [c]@-}
subArrayR :: Array a -> Int -> Int -> Int -> Array a
subArrayR xs n m 0 = make (m-n) (get xs 0)  
subArrayR xs n m c = set (subArrayR xs n m (c-1)) (c-1) (get xs (n+c-1))

{-@ reflect subArray @-}
{-@ subArray :: xs:{size xs >= 1} -> n:{v:Nat | v <= size xs} -> m:{v:Nat | n <= m && m <= size xs} -> ys:{size ys == m-n}@-}
subArray :: Array a -> Int -> Int -> Array a
subArray xs n m = subArrayR xs n m (m-n)


-- n > m
{-@ lma_set_equal :: xs:_ -> x:_ -> n:{v:Nat | v < size xs} -> m:{v:Nat | v <= n} 
      -> {(toSet (set xs n x) m == toSet xs m)} / [m] @-}
lma_set_equal :: Ord a => Array a -> a -> Int -> Int -> Proof
lma_set_equal xs x n 0 = ()
lma_set_equal xs x n m
  = toSet (set xs n x) m
  -- === S.union (S.singleton (get (set xs n x) (m-1))) (toSet (set xs n x) (m-1))
    ? (lma_gns xs n (m-1) x)
  -- === S.union (S.singleton (get xs (m-1))) (toSet (set xs n x) (m-1))
    ? (lma_set_equal xs x n (m-1))
  -- === S.union (S.singleton (get xs (m-1))) (toSet xs (m-1))
  === toSet xs m
  *** QED