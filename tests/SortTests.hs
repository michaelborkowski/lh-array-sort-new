
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE LinearTypes         #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SortTests (sortTests) where

import           Test.Tasty
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import           Test.Tasty.HUnit
import           Text.Printf (printf)

import           Data.List (sort)

import           Array
import           Insertion (isort_top)
import qualified DpsMergeSort4 as M4
import qualified DpsMergeSort4Par as M4Par
import qualified PiecewiseFallbackSort as PF
import qualified PiecewiseFallbackSortPar as PFPar
import           QuickSort (quickSort)

import Test.Tasty.Runners (FailureReason(TestThrewException))
import           Linear.Common

type LinearSort = Array Int -. Array Int

---------------------------------------------------------
--BAD SORTS 
---------------------------------------------------------
-- Function to sort and increment the first element
incrementFirstElement :: [Int] -> [Int]
incrementFirstElement xs =
  case sorted of
    [] -> []
    _  -> Prelude.take index sorted ++ [sorted !! index + 1] ++ Prelude.drop (index + 1) sorted
  where
    sorted = sort xs
    index = 0

-- Function to sort and increment the middle element
incrementMiddleElement :: [Int] -> [Int]
incrementMiddleElement xs =
  case sorted of
    [] -> []
    _  -> Prelude.take index sorted ++ [sorted !! index + 1] ++ Prelude.drop (index + 1) sorted
  where
    sorted = sort xs
    index = length sorted `div` 2

-- Function to sort and increment the last element
incrementLastElement :: [Int] -> [Int]
incrementLastElement xs =
  case sorted of
    [] -> []
    _  -> Prelude.take index sorted ++ [sorted !! index + 1] ++ Prelude.drop (index + 1) sorted
  where
    sorted = sort xs
    index = length sorted - 1

-- Function to sort and remove a random element
removeRandomElement :: [Int] -> [Int]
removeRandomElement xs =
  case sorted of
    [] -> []
    _  -> Prelude.take idx sorted ++ Prelude.drop (idx + 1) sorted
  where
    sorted = sort xs
    idx = length sorted `div` 2 -- Hardcoded "random" index

-- Function to sort and add a new random element
addRandomElement :: [Int] -> [Int]
addRandomElement xs =
  let sorted = sort xs
  in sorted ++ [42] -- Hardcoded extra element for deterministic testing

-- Function to sort and displace an element (making it unsorted)
displaceElement :: [Int] -> [Int]
displaceElement xs =
  case sorted of
    [] -> []
    [x] -> [x]
    (x:y:zs) -> y : x : zs -- Swaps first two elements
  where
    sorted = sort xs

---------------------------------------------------------
--SORT PROPERTIES
---------------------------------------------------------
-- Property: Function correctly sorts all elements
sortsCorrectlyProperty :: ([Int] -> [Int]) -> [Int] -> Bool
sortsCorrectlyProperty sortFunc xs = sort xs == sortFunc xs

-- Property: Function correctly sorts all elements linearly
-- Excludes arrays of length <= 1 to satisfy the refinement type constraints of Insertion Sort
{-@ sortsCorrectlyPropertyLinear :: LinearSort
                                 -> {xs: [Int] | len xs >= 0}
                                 -> Bool @-}
sortsCorrectlyPropertyLinear :: (Array Int -. Array Int) -> [Int] -> Bool
sortsCorrectlyPropertyLinear sortFunc xs = 
  if length xs > 1 then sort xs == toList (sortFunc (fromList xs))
  else True

-- These Properties are probably not necessary to explicity test since we can directly compare to sort
-- -- Property: Sorting preserves all elements
-- preservesElementsProperty :: ([Int] -> [Int]) -> [Int] -> Bool
-- preservesElementsProperty sortFn xs = sort xs == sort (sortFn xs)

-- -- Property: Sorted array is ordered
-- sortOrderedProperty :: ([Int] -> [Int]) -> [Int] -> Bool
-- sortOrderedProperty sortFn xs = isSorted (sortFn xs)
--   where
--     isSorted [] = True
--     isSorted [_] = True
--     isSorted (y:z:zs) = y <= z && isSorted (z:zs)

---------------------------------------------------------
--TESTS
---------------------------------------------------------
-- Test sorts
-- Run tests with "cabal run tests --flag=-liquid-checks"
sortTests :: TestTree
sortTests = testGroup "Sorting Tests" [
  testFailingSorts,
  testWorkingSorts
  ] where

  -- Tests that bad sorts fail the sorts correctly property check
  testFailingSorts :: TestTree
  testFailingSorts = testGroup "Test Failing Sorts" [
    QC.testProperty "Increment First Element fails prop_sortPreservesElements" $
      QC.expectFailure (sortsCorrectlyProperty incrementFirstElement),

    QC.testProperty "Increment Middle Element does not correctly sort" $
      QC.expectFailure (sortsCorrectlyProperty incrementMiddleElement),

    QC.testProperty "Increment Last Element does not correctly sort" $
      QC.expectFailure (sortsCorrectlyProperty incrementLastElement),

    QC.testProperty "Remove Random Element does not correctly sort" $
      QC.expectFailure (sortsCorrectlyProperty removeRandomElement),

    QC.testProperty "Add Random Element does not correctly sort" $
      QC.expectFailure (sortsCorrectlyProperty addRandomElement),

    QC.testProperty "Displace Element does not correctly sort" $
      QC.expectFailure (sortsCorrectlyProperty displaceElement)
    ]

  -- Tests that our custom sorts work properly
  testWorkingSorts :: TestTree
  testWorkingSorts = testGroup "Test Working Sorts" [
    testSort "Insertion Sort" isort_top,
    testSort "Dps Merge Sort 4" M4.msort,
    testSort "Dps Merge Sort 4 Par" M4Par.msort,
    testSort "Piecewise Fallback Sort" PF.pfsort,
    testSort "Piecewise Fallback Sort Par" PFPar.pfsort,
    testSort "Quick Sort" quickSort
    ] where

    -- Generates a test for a given sorting algorithm
    {-@ testSort :: String -> LinearSort -> TestTree @-}
    testSort :: String -> (Array Int -. Array Int) -> TestTree
    testSort name sortFunc = testGroup ("Sorting Tests: " ++ name) [
      QC.testProperty "Correctly Sorts Array" (sortsCorrectlyPropertyLinear sortFunc)
      ]

-- -- Test array functionality
-- -- Run tests with "cabal run tests --flag=-liquid-checks"
-- sortTests :: TestTree
-- sortTests = testGroup "Array Tests" [ {-testArbitrary,-} testBaseSort {-, testCilk, testDpsMerge, testDpsMergePar, testDpsMergeParSeqFallback, testDpsMergeSort, testDpsMergeSort4, testDpsMergeSort4Par, testDpsMergeSortPar, testQuickSort, testQuickSortCilk-} ] where
--   performanceTestMultiplier = 1

--   -- Prints an array
--   printArray :: (Show a) => Array a -> IO ()
--   printArray arr = mapM_ print (toList arr)

--   -- Prints random arrays so they could be visually inspected
--   testArbitrary = QC.testProperty "Test Arbitrary" $ 
--     QC.forAll QC.arbitrary $ \(randomArr :: Array Int) -> 
--       QC.ioProperty $ do
--         printArray randomArr
--         return True

--   -- Tests for the base sort everything is compared against
--   testBaseSort :: TestTree
--   testBaseSort = testGroup "Test Base Sort" [ {-visualTests-}{-, performanceTests,-} propertyTests] where

--     -- Visual tests for the base sort
--     -- These may need to be commented after running once to reduce output bloat
--     visualTests :: TestTree
--     visualTests = testGroup "Base Sort Visual Tests" [ printSorted ] where

--       -- Prints the an array using the default sort so the sort can be visually checked
--       printSorted :: TestTree
--       printSorted = QC.testProperty "Base Print Sorted" $
--         QC.forAll QC.arbitrary $ \(randomArr :: Array Int) ->
--           QC.ioProperty $ do
--             let elements = toList randomArr
--             let sortedElements = sort elements
--             let maxWidth = maximum $ map (length . show) elements
--             putStrLn "Array Start:"
--             mapM_ (printPair maxWidth) (zip elements sortedElements)
--             putStrLn "Array End."
--             putStrLn ""
--           where
--             printPair width (e, s) = putStrLn (printf "| %-*s | %-*s |" width (show e) width (show s))

--     -- Property tests for the base sort
--     -- Testing sorting by checking that every element is in ascending order and that the elements are the same before and after the sort
--     propertyTests :: TestTree
--     propertyTests = testGroup "Base Sort Property Tests"
--       [ QC.testProperty "Sorting preserves elements" prop_sortPreservesElements
--       , QC.testProperty "Sorting produces ordered array" prop_sortOrdered
--       ]

--     -- Property: Sorting preserves all elements
--     prop_sortPreservesElements :: [Int] -> Bool
--     prop_sortPreservesElements xs = sort xs == sort (toList $ fromList xs)

--     -- Property: Sorted array is ordered
--     prop_sortOrdered :: [Int] -> Bool
--     prop_sortOrdered xs = isSorted (toList $ fromList $ sort xs)
--       where
--         isSorted [] = True
--         isSorted [_] = True
--         isSorted (y:z:zs) = y <= z && isSorted (z:zs)


{-   -- Property that everything is in increasing order
  AscendingOrderProperty :: QC.Property

-- Tests for the base sort
    testBaseSort :: TestTree
    testBaseSort = testGroup "Test Base Sort"
      [ propertyTests ]
      where
        -- Property tests to verify sorting correctness
        propertyTests :: TestTree
        propertyTests = testGroup "Base Sort Property Tests"
          [ QC.testProperty "Sorting preserves elements" prop_sortPreservesElements
          , QC.testProperty "Sorting produces ordered array" prop_sortOrdered
          ]

        -- Property: Sorting preserves all elements
        prop_sortPreservesElements :: [Int] -> Bool
        prop_sortPreservesElements xs = sort xs == sort (toList $ fromList xs)

        -- Property: Sorted array is ordered
        prop_sortOrdered :: [Int] -> Bool
        prop_sortOrdered xs = isSorted (toList $ fromList $ sort xs)
          where
            isSorted [] = True
            isSorted [_] = True
            isSorted (y:z:zs) = y <= z && isSorted (z:zs)
-}
