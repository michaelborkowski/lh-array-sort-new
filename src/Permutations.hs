{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}


-- {-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

-- assuming the array has distinct values
module Permutations where

import           Language.Haskell.Liquid.ProofCombinators
import qualified Data.Set as S
import           Array as A
 
{-@ type Maps I J = { x:Int | I <= x && x < J } -> { y:Int | I <= y && y < j } @-}
type Maps = Int -> Int

{-@ type Perms I J = { f:(Maps I J) | bijective I J f } @-}

{-@ reflect bijective @-}
{-@ bijective :: { i:Int | 0 <= i } -> { j:Int | i <= j } -> f:(Maps i j) -> Bool @-}
bijective :: Int -> Int -> Maps -> Bool
bijective i j f = goBijective i j f i S.empty

{-@ reflect goBijective @-}
{-@ goBijective :: { i:Int | 0 <= i } -> { j:Int | i <= j } -> f:(Maps i j) 
                -> { k:Int | i <= k && k <= j } -> S.Set Int -> Bool / [ j - k ] @-}
goBijective :: Int -> Int -> Maps -> Int -> S.Set Int -> Bool
goBijective i j f k acc 
  | k == j    =  True
  | otherwise =  not (S.member (f k) acc) && goBijective i j f (k+1) (S.union (S.singleton (f k)) acc)

{-
{-@ measure propOf :: a -> b @-}
{-@ type ProofOf E = { proofObj:_ | propOf proofObj = E } @-}

data EquivP where
    Equiv :: Array a -> Array a -> EquivP

data Equiv where
  -}  


-- {-@ reflect toBag @-}
-- {-@ toBag :: xs:_ -> n:{v:Nat | v <= size xs}
--        -> s:_ / [n] @-}
-- toBag :: Ord a => Array a -> Int -> B.Bag a
-- toBag xs 0 = B.empty
-- toBag xs n = B.union (B.singleton (A.get xs (n-1))) (toBag xs (n-1))

-- {-@ reflect equalP @-}
-- equalP :: Ord a => Array a -> Array a -> Bool
-- equalP xs ys = (toBag xs (size xs)) == (toBag ys (size ys))

