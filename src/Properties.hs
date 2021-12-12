{-@ LIQUID "--reflection"   @-}
{-@ LIQUID "--ple"          @-}
{-@ LIQUID "--short-names"  @-}

module Properties where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators
import           Array
import           Equivalence

  -- | This module abstracts reasoning about properties of individual array elements.

{-@ type Property a = x1:a -> Bool @-}
type Property a = (a -> Bool)  -- predicates 

{- @ type Property a = xs:(Array a) -> { i:Int | 0 <= i && i < size xs } -> Bool @-}
--type Property a = (Array a -> Int -> Bool)  -- predicates 

{-@ reflect rangeProperty @-}
{-@ rangeProperty :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i <= j && j <= size xs }
                                  -> p:(Property a) -> Bool / [j - i] @-}
rangeProperty :: Array a -> Int -> Int -> Property a -> Bool
rangeProperty xs i j p | i == j    = True
                       | otherwise = (p (get xs i)) && rangeProperty xs (i+1) j p

{-@ lem_rangeProperty_right :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i < j && j <= size xs }
                            -> { p:(Property a) | rangeProperty xs i j p }
                            -> { pf:_  | p (get xs (j-1)) && rangeProperty xs i (j-1) p } / [ j - i ] @-}
lem_rangeProperty_right :: Array a -> Int -> Int -> Property a -> Proof
lem_rangeProperty_right xs i j p | i + 1 == j  = ()
                                 | otherwise   = () ? lem_rangeProperty_right xs (i+1) j p

{-@ lem_rangeProperty_build_right :: xs:(Array a) -> p:(Property a) -> { i:Int | 0 <= i } 
                                  -> { j:Int | i <= j && j <= size xs &&
                                               rangeProperty xs i j p && p (get xs j) }
                                  -> { pf:_ | rangeProperty xs i (j+1) p } / [j-i] @-}
lem_rangeProperty_build_right :: Array a -> Property a -> Int -> Int -> Proof
lem_rangeProperty_build_right xs p i j | i == j     = ()
                                       | otherwise  = () ? lem_rangeProperty_build_right xs p (i+1) j

--                                         -> { p:(Property a) | rangeProperty xs i j p }
{-@ lem_rangeProperty_at :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i < j && j <= size xs }
                                         -> p:(Property a) 
                                         -> { k:Int | i <= k && k < j && rangeProperty xs i j p } 
                                         -> { pf:_  | p (get xs k) } / [ j - i ] @-}
lem_rangeProperty_at :: Array a -> Int -> Int -> Property a -> Int -> Proof
lem_rangeProperty_at xs i j p k | i == k     = ()
                                | otherwise  = () ? lem_rangeProperty_at xs (i+1) j p k 


{-@ lem_bagBtw_pres_rangeProperty :: xs:(Array a) -> { ys:(Array a) | size xs == size ys }
                                  -> { i:Int | 0 <= i } 
                                  -> { j:Int | i <= j && j <= size xs && toBagBtw xs i j == toBagBtw ys i j }
                                  -> { p:(Property a) | rangeProperty xs i j p }
                                  -> { pf:Proof       | rangeProperty ys i j p } @-}
lem_bagBtw_pres_rangeProperty :: Ord a => Array a -> Array a -> Int -> Int -> Property a -> Proof
lem_bagBtw_pres_rangeProperty xs ys i j p = go_pres_rangeProperty i
  where
    {-@ go_pres_rangeProperty :: { k:Int | i <= k && k <= j } -> { pf:_ | rangeProperty ys k j p } / [j-k] @-}
    go_pres_rangeProperty k | k == j    = ()
                            | otherwise = let k' = lem_equal_toBagBtw_index ys xs i j k
                                           in () ? lem_rangeProperty_at xs i j p k'
                                                 ? go_pres_rangeProperty (k+1)


