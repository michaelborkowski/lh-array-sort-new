{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}
-- {-@ LIQUID "--checks=lma_msort" @-}


-- {-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Insertion where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
-- import qualified Data.Set as S
-- import           Expressions 
import           Imp  
import           BigStep
import           Array
import           Order



--------------------------------------------------------------------------------
-- | Implementations
--------------------------------------------------------------------------------

-- input xs needs to have one extra space at the end. 
{-@ reflect insert @-}
{-@ insert :: xs:_ -> x:_ -> n:{v:Nat | v < size xs}
       -> ys:{size ys == size xs} / [n] @-}

insert :: Ord a => Array a -> a -> Int -> Array a
insert xs x 0 =  set xs 0 x -- first element is sorted
insert xs x n               -- sort the nth element into the first n+1 elements
  | x < (get xs (n-1)) = insert (set xs (n) (get xs (n-1))) x (n-1)
  | otherwise      = set xs n x

-- >>>  isort (fromList [1,3,2,9,6,0,5,2,10,-1]) 9
{-@ reflect isort @-}
{-@ isort :: xs:_ -> n:{v:Nat | v < size xs}
      -> ys:{size ys == size xs} / [n] @-}
isort :: Ord a => Array a -> Int -> Array a
isort xs n 
  | (size xs == 0) = xs
  | (size xs == 1) = xs
  | (n == 0)       = make (size xs) (get xs 0)
  | otherwise      = insert (isort xs (n-1)) (get xs n) n


--------------------------------------------------------------------------------
-- | Proofs
--------------------------------------------------------------------------------
{-@ lma_insert :: xs:_ -> x:_ -> n:{v:Nat | v < size xs && (isSortedFstN xs (v))}
      -> ys:{isSortedFstN (insert xs x n) (n+1)} / [n] @-}
lma_insert :: Ord a => Array a -> a -> Int -> Proof
lma_insert xs x 0 = ()
lma_insert xs x n 
  | x < (get xs (n-1)) 
    = isSortedFstN (insert xs x n) (n+1)
    === isSortedFstN (insert (set xs (n) (get xs (n-1))) x (n-1)) (n+1)
    === isSortedFstN (insert (set xs (n) (get xs (n-1))) x (n-1)) (n+1)
