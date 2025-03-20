{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MonoLocalBinds #-}

module Properties (module Properties) where

import qualified Test.Tasty.QuickCheck as QC

import qualified Data.Array as StandardArray
import qualified Array as CustomArray
import qualified ArrayOperations as CustomOperations
import           Linear.Common
import           Data.List (sort)

type LinearSort = CustomArray.Array Int -. CustomArray.Array Int
--------------------------------------------------------------------------------

-- Real swapCommutativeProperty.
-- Define the commutative property for swap.
swapCommutativeProperty :: (QC.Arbitrary a, CustomArray.HasPrim a, Show a, Eq a) => CustomArray.Array a -> Int -> Int -> QC.Property
swapCommutativeProperty arr i j =
  i /= j QC.==> CustomArray.toList (CustomOperations.swap arr i j) QC.=== CustomArray.toList (CustomOperations.swap arr j i)

-- Property: Function correctly sorts all elements.
sortsCorrectlyProperty :: ([Int] -> [Int]) -> [Int] -> Bool
sortsCorrectlyProperty sortFunc xs = sort xs == sortFunc xs

-- Property: Function correctly sorts all elements linearly.
-- Excludes arrays of length <= 1 to satisfy the constraints of Insertion Sort.
{-@ sortsCorrectlyPropertyLinear :: LinearSort
                                 -> {xs: [Int] | len xs >= 0}
                                 -> Bool @-}
sortsCorrectlyPropertyLinear :: (CustomArray.Array Int -. CustomArray.Array Int) -> [Int] -> Bool
sortsCorrectlyPropertyLinear sortFunc xs = 
  if length xs > 1 then sort xs == CustomArray.toList (sortFunc (CustomArray.fromList xs))
  else True