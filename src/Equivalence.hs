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
-- import qualified State as S
-- import qualified Data.Set as S
import           Language.Haskell.Liquid.Bag as B
-- import           Expressions 
-- import           Imp 
-- import           BigStep
import           Array as A
 

-- {-@ reflect toBag @-}
-- {-@ toBag :: xs:_ -> n:{v:Nat | v <= size xs}
--        -> s:_ / [n] @-}
-- toBag :: Ord a => Array a -> Int -> B.Bag a
-- toBag xs 0 = B.empty
-- toBag xs n = B.union (B.singleton (A.get xs (n-1))) (toBag xs (n-1))

{-@ reflect toBag @-}
{-@ toBag :: xs:_ -> n:{v:Nat | v <= 0}
       -> s:_ / [n] @-}
toBag :: Ord a => Array a -> Int -> B.Bag a
toBag xs 0 = B.empty
-- toBag xs n = B.put (A.get xs (n-1)) (toBag xs (n-1))

-- {-@ reflect equalP @-}
-- equalP :: Ord a => Array a -> Array a -> Bool
-- equalP xs ys = (toBag xs (size xs)) == (toBag ys (size ys))

{-@ reflect subArrayR @-}
{-@ subArrayR :: xs:{size xs >= 1} -> n:{v:Nat | v <= size xs} -> m:{v:Nat | n <= m && m <= size xs} -> c:{v:Nat | v <= m-n} -> ys:{size ys == m-n} / [c]@-}
subArrayR :: Array a -> Int -> Int -> Int -> Array a
subArrayR xs n m 0 = make (m-n) (A.get xs 0)  
subArrayR xs n m c = set (subArrayR xs n m (c-1)) (c-1) (A.get xs (n+c-1))

{-@ reflect subArray @-}
{-@ subArray :: xs:{size xs >= 1} -> n:{v:Nat | v <= size xs} -> m:{v:Nat | n <= m && m <= size xs} -> ys:{size ys == m-n}@-}
subArray :: Array a -> Int -> Int -> Array a
subArray xs n m = subArrayR xs n m (m-n)


-- -- n > m
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
