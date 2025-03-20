{-# LANGUAGE CPP                 #-}
{-# LANGUAGE TypeOperators       #-}

module SortTests (sortTests) where

import           Test.Tasty
import qualified Test.Tasty.QuickCheck as QC
import           Test.Tasty.HUnit
import           Text.Printf (printf)
import           Data.List (sort)

import           Infra
import           InvalidSorts
import           Properties
import           Array
import           Insertion (isort_top')
import qualified DpsMergeSort4 as M4
import qualified DpsMergeSort4Par as M4Par
import qualified PiecewiseFallbackSort as PF
import qualified PiecewiseFallbackSortPar as PFPar
import           QuickSort (quickSort)

import           Linear.Common

type LinearSort = Array Int -. Array Int
--------------------------------------------------------------------------------

-- Test sorts.
-- Run tests with "cabal run tests --flag=-liquid-checks".
sortTests :: TestTree
sortTests = testGroup "Sorting Tests" [
  testFailingSorts,
  testWorkingSorts
  ] where

  -- Tests that bad sorts fail the sorts correctly property check.
  testFailingSorts :: TestTree
  testFailingSorts = testGroup "Test Failing Sorts" [
    QC.testProperty "Increment First Element fails prop_sortPreservesElements" $
      QC.expectFailure (sortsCorrectlyProperty incrementFirstElement),

    QC.testProperty "Increment Middle Element does not correctly sort" $
      QC.expectFailure (sortsCorrectlyProperty incrementMiddleElement),

    QC.testProperty "Increment Last Element does not correctly sort" $
      QC.expectFailure (sortsCorrectlyProperty incrementLastElement),

    QC.testProperty "Remove Random Element does not correctly sort" $
      QC.expectFailure (sortsCorrectlyProperty removeElement),

    QC.testProperty "Add Random Element does not correctly sort" $
      QC.expectFailure (sortsCorrectlyProperty addElement),

    QC.testProperty "Displace Element does not correctly sort" $
      QC.expectFailure (sortsCorrectlyProperty displaceElement)
    ]

  -- Tests that our custom sorts work properly.
  testWorkingSorts :: TestTree
  testWorkingSorts = testGroup "Test Working Sorts" [
    testSort "Insertion Sort" isort_top'
-- TODO: these should be fixed eventually; but first look at the TODOs in ArrayTests...
#ifndef MUTABLE_ARRAYS
    , testSort "Quick Sort" quickSort
#endif
#ifndef PRIM_MUTABLE_ARRAYS
    , testSort "Dps Merge Sort 4" M4.msort
    , testSort "Dps Merge Sort 4 Par" M4Par.msort
#endif
    , testSort "Piecewise Fallback Sort" PF.pfsort
    , testSort "Piecewise Fallback Sort Par" PFPar.pfsort
    ] where

    -- Generates a test for a given sorting algorithm.
    {-@ testSort :: String -> LinearSort -> TestTree @-}
    testSort :: String -> (Array Int -. Array Int) -> TestTree
    testSort name sortFunc = testGroup ("Sorting Tests: " ++ name) [
      QC.testProperty "Correctly Sorts Array" (sortsCorrectlyPropertyLinear sortFunc)
      ]
