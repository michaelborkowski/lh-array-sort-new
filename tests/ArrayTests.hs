{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}

module ArrayTests (arrayTests) where

import           Test.Tasty
import qualified Test.Tasty.QuickCheck as QC
import           Test.Tasty.HUnit
import           System.Random (Random)

import Infra
    ( valueSwapTest,
      checkInvalid2,
      checkInvalid3,
      makeStandardArray)
import           Properties
import           Control.Monad
import qualified Data.Array as StandardArray
import qualified Array as CustomArray
import qualified ArrayOperations as CustomOperations
--------------------------------------------------------------------------------

-- Global constants
performanceTestMultiplier = 1
mediumNumber = 1000 -- Used for array size
smallNumber = 100 -- Used for number of operations on array

-- Entry point
arrayTests :: TestTree
arrayTests = testGroup "Array Tests"
  [
    testMakeArray
  , testArrayGetSet
  , testSwap
  , testSplit
  ]


--------------------------------------------------------------------------------
--
--                      Tests for the makeArray function.
--
-- Tests that size is correct with explicit tests for size 0 and 1.
-- Tests that all the values are correct with explicit tests for size 0 and 1.
-- On the pure backend, tests that negative arrays can't be made.
--
--------------------------------------------------------------------------------
testMakeArray :: TestTree
testMakeArray = testGroup "MakeArray Tests"
  [ caseTests
-- TODO: property tests should work for mutable backends too (?)
#ifndef MUTABLE_ARRAYS
  , propertyTests
#endif
  , invalidOperationTests
  ] where

  -- The case tests for the MakeArray function.
  -- Tests that arrays of size 0 and 1 have the proper size and elements.
  caseTests :: TestTree
  caseTests = testGroup "MakeArray Case Tests"
    [ testEmptyArray
-- TODO: the below should work for mutable backends too (?)
#ifndef MUTABLE_ARRAYS
    , testSizeOneArray
#endif
    ]
    where

    -- Testing the output of an empty array.
    testEmptyArray = QC.testProperty "Test Empty Array" $
      QC.forAll QC.arbitrary $ \(randomElement :: Int) ->
          let customArr = CustomArray.makeArray 0 randomElement
              standardArr = makeStandardArray 0 randomElement
          in CustomArray.size customArr QC.=== 0 QC..&. CustomArray.toList customArr QC.=== StandardArray.elems standardArr

    -- Testing the output of an array with one elemennt.
    testSizeOneArray = QC.testProperty "Test Size One Array" $
      QC.forAll QC.arbitrary $ \(randomElement :: Int) ->
          let customArr = CustomArray.makeArray 1 randomElement
              standardArr = makeStandardArray 1 randomElement
          in CustomArray.size customArr QC.=== 1 QC..&. CustomArray.toList customArr QC.=== StandardArray.elems standardArr


  -- The property tests for the makeArray function.
  -- Tests that random arrays have proper size and elements.
  propertyTests :: TestTree
  propertyTests = testGroup "MakeArray Property Tests"
    [ testRandomSizeArray ]
    where

    -- Testing the output of a random size array.
    testRandomSizeArray = QC.testProperty "Test Random Size Array" $
      QC.forAll ((,) <$> QC.chooseInt (0, mediumNumber) <*> QC.arbitrary) $ \(randomSize :: Int, randomElement :: Int) ->
          let customArr = CustomArray.makeArray randomSize randomElement
              standardArr = makeStandardArray randomSize randomElement
          in CustomArray.size customArr QC.=== randomSize QC..&. CustomArray.toList customArr QC.=== StandardArray.elems standardArr

  -- The tests for exception cases of the MakeArray functions.
  -- Tests that negative size arrays can't be made.
  invalidOperationTests :: TestTree
  invalidOperationTests = testGroup "MakeArray Invalid Operation Tests"
    [ testNegativeSizeArray ]
    where

    -- Testing a negative size array.
    testNegativeSizeArray :: TestTree
    testNegativeSizeArray =
      checkInvalid2 "Negative size array is invalid" 1000
      (CustomArray.makeArray :: Int -> Int -> CustomArray.Array Int) (-5) 1


--------------------------------------------------------------------------------
--
--                    Tests for get / set.
--
-- Tests that getting and setting values works for the first and last indices.
-- Tests random combinations of gets and sets.
-- On the pure backend, tests getting/setting negative and out of bounds elements.
-- Explicitly tests size 0 array.
--
--------------------------------------------------------------------------------
testArrayGetSet :: TestTree
testArrayGetSet = testGroup "Array Get/Set Tests"
  [
    caseTests
#ifndef MUTABLE_ARRAYS
  , propertyTests
  , invalidOperationTests
#endif
  ] where

  -- The case tests for the get and set functions.
  -- Tests that getting and setting values works for the first and last indices.
  caseTests :: TestTree
  caseTests = testGroup "Array Get/Set Case Tests"
    [ testFirstIndex, testLastIndex ]
    where

    -- Testing the get and set functions with valid indices.
    testFirstIndex = QC.testProperty "Test Get/Set First Index" $
      QC.forAll QC.arbitrary $ \(size :: Int, startValue :: Int, newValue :: Int) ->
        if size > 0 then
          let index = 0
              customArr = CustomArray.makeArray size startValue
              updatedArr = CustomArray.set customArr index newValue
              fetchedValue = CustomArray.get updatedArr index
          in fetchedValue QC.=== newValue
        else
          QC.property True

    -- Testing setting an out-of-bounds index (no effect should occur).
    testLastIndex = QC.testProperty "Test Get/Set Last Index" $
      QC.forAll QC.arbitrary $ \(size :: Int, startValue :: Int, newValue :: Int) ->
        if size > 0 then
          let index = max 0 (size - 1)
              customArr = CustomArray.makeArray size startValue
              updatedArr = CustomArray.set customArr index newValue
              fetchedValue = CustomArray.get updatedArr index
          in fetchedValue QC.=== newValue
        else
          QC.property True

  -- The property tests for the get and set functions.
  -- Tests that the set operation works correctly for random values.
  propertyTests :: TestTree
  propertyTests = testGroup "Array Get/Set Property Tests"
    [testRandomGetSet]
    where

    -- Testing random set and get operations.
    testRandomGetSet = QC.testProperty "Test Random Get/Set Operations" $
      QC.forAll ((,,) <$> QC.chooseInt (1, mediumNumber) <*> QC.chooseInt (1, smallNumber) <*> QC.chooseAny) $ \(size :: Int, numOperations :: Int, startVal :: Int) ->
        QC.forAll (QC.vectorOf numOperations ((,) <$> QC.chooseInt (0, size - 1) <*> QC.chooseAny)) $ \randomUpdates ->
          QC.forAll (QC.vectorOf numOperations (QC.chooseInt (0, size - 1))) $ \randomGetIndices ->
            let
                -- Helper functions to perform multiple set operations
                performSetsCustom :: CustomArray.Array Int -> [(Int, Int)] -> CustomArray.Array Int
                performSetsCustom arr [] = arr
                performSetsCustom arr ((index, value):xs) = performSetsCustom (CustomArray.set arr index value) xs

                performSetsStandard :: StandardArray.Array Int Int -> [(Int, Int)] -> StandardArray.Array Int Int
                performSetsStandard arr [] = arr
                performSetsStandard arr ((index, value):xs) = performSetsStandard (arr StandardArray.// [(index, value)]) xs

                -- Performing sets
                customArr = CustomArray.makeArray size startVal
                standardArr = makeStandardArray size startVal
                updatedCustomArr = performSetsCustom customArr randomUpdates
                updatedStandardArr :: StandardArray.Array Int Int
                updatedStandardArr = performSetsStandard standardArr randomUpdates

                -- Performing gets
                customGets = map (CustomArray.get updatedCustomArr) randomGetIndices
                standardGets = map (updatedStandardArr StandardArray.!) randomGetIndices
            in QC.property $
                CustomArray.size updatedCustomArr QC.=== size QC..&.
                CustomArray.toList updatedCustomArr QC.=== StandardArray.elems updatedStandardArr QC..&.
                customGets QC.=== standardGets

  -- The tests for exception cases of the get and set functions.
  -- Tests getting/setting negative and out-of-bounds indices.
  -- Tests getting/setting with empty arrays.
  -- NOTE: doesn't apply to mutable backends, which don't have bounds checking
  invalidOperationTests :: TestTree
  invalidOperationTests = testGroup "Array Get/Set Invalid Operation Tests"
    [ testNegativeIndexGet, testNegativeIndexSet, testOutOfBoundsIndexGet, testOutOfBoundsIndexSet,
      testEmptyArraySet, testEmptyArrayGet ]
    where

    -- Testing getting a negative index.
    testNegativeIndexGet :: TestTree
    testNegativeIndexGet =
      checkInvalid2 "Negative index is invalid for get" 100
      (CustomArray.get :: CustomArray.Array Int -> Int -> Int) (CustomArray.makeArray 5 0) (-1)

    -- Testing setting a negative index.
    testNegativeIndexSet :: TestTree
    testNegativeIndexSet =
      checkInvalid3 "Negative index is invalid for set" 100
      (CustomArray.set :: CustomArray.Array Int -> Int -> Int -> CustomArray.Array Int) (CustomArray.makeArray 5 0) (-1) 1

    -- Testing getting an out-of-bounds index.
    testOutOfBoundsIndexGet :: TestTree
    testOutOfBoundsIndexGet =
      checkInvalid2 "Out-of-bounds index is invalid for get" 100
      (CustomArray.get :: CustomArray.Array Int -> Int -> Int) (CustomArray.makeArray 5 0) 5

    -- Testing setting an out-of-bounds index.
    testOutOfBoundsIndexSet :: TestTree
    testOutOfBoundsIndexSet =
      checkInvalid3 "Out-of-bounds index is invalid for set" 100
      (CustomArray.set :: CustomArray.Array Int -> Int -> Int -> CustomArray.Array Int) (CustomArray.makeArray 5 0) 5 1

    -- Testing get on an empty array.
    testEmptyArrayGet :: TestTree
    testEmptyArrayGet =
      checkInvalid2 "Out-of-bounds index is invalid for get" 100
      (CustomArray.get :: CustomArray.Array Int -> Int -> Int) (CustomArray.makeArray 0 0) 0

    -- Testing set on an empty array.
    testEmptyArraySet :: TestTree
    testEmptyArraySet =
      checkInvalid3 "Out-of-bounds index is invalid for set" 100
      (CustomArray.set :: CustomArray.Array Int -> Int -> Int -> CustomArray.Array Int) (CustomArray.makeArray 0 0) 0 1


--------------------------------------------------------------------------------
--
--                      Tests for the swap function.
--
--------------------------------------------------------------------------------
testSwap :: TestTree
testSwap = testGroup "Swap Tests" [ caseTests, performanceTests, propertyTests ] where

  -- The case tests for the swap function.
  caseTests :: TestTree
  caseTests = testGroup "Swap Case Tests" [
      testValuesSwapped1
    , testValuesSwapped2
    , testValuesSwapped3
    , testValuesSwapped4
-- TODO: the below should work for mutable backends too
#ifndef MUTABLE_ARRAYS
    , testSwapSameIndex
#endif
    ] where

    -- Testing if swapping two elements works correctly.
    testValuesSwapped1 :: TestTree
    testValuesSwapped1 = testCase "Test Values Swapped Manual" $ do
      let arr = CustomArray.makeArray 5 (0 :: Int)
      let arr1 = CustomArray.set arr 0 1
      let arr2 = CustomArray.set arr1 1 2
      let swappedArr = CustomOperations.swap arr2 0 1
      assertEqual "First element should be 2" 2 (CustomArray.get swappedArr 0)
      assertEqual "Second element should be 1" 1 (CustomArray.get swappedArr 1)

    -- Testing if swapping two elements works correctly.
    testValuesSwapped2 = valueSwapTest 5 0 0 1 1 (2 :: Int)
    testValuesSwapped3 = valueSwapTest 10 1 1 2 2 (4 :: Int)
    testValuesSwapped4 = valueSwapTest 20 1 2 3 4 (5 :: Int)

    -- Testing that swapping an element with itself doesn't change anything.
    testSwapSameIndex :: TestTree
    testSwapSameIndex = testCase "Test Swapping Same Index" $ do
      let arr = CustomArray.makeArray 5 (1 :: Int)
      let swappedArr = CustomOperations.swap arr 2 2
      assertEqual "Array should remain unchanged" 1 (CustomArray.get swappedArr 2)

  -- Test performance for swap.
  performanceTests :: TestTree
  performanceTests = testGroup "Swap Performance Tests" [ testLargeArraySwap ] where
    largeInt = 1000000 * performanceTestMultiplier

    -- Test performance of creating and splitting a large.
    testLargeArraySwap :: TestTree
    testLargeArraySwap = testCase "Test Large Array Swap" $ do
      let largeArr = CustomArray.makeArray largeInt (0 :: Int)
      let updatedArr = CustomArray.set largeArr (largeInt-1) 1
      let swappedArr = CustomOperations.swap updatedArr (largeInt-1) 0
      assertEqual "Last element should be 0" 0 (CustomArray.get swappedArr (largeInt-1))

  -- The property tests for the split function.
  propertyTests :: TestTree
  propertyTests = testGroup "Swap Property Tests" [
-- TODO: the below should work for mutable backends too
#ifndef MUTABLE_ARRAYS
    testSwapCommutative
#endif
    ] where

    -- Generates random arrays to test that swap is commutative.
    testSwapCommutative :: TestTree
    testSwapCommutative = QC.testProperty "Swapping two elements is commutative"
      $ QC.forAll QC.arbitrary $ \(array :: CustomArray.Array Int) ->
        let size = CustomArray.size array in
          if size < 2 then 1 QC.=== 1
          else
            QC.forAll ( QC.chooseInt (0, size - 1) ) $ \i ->
              QC.forAll ( QC.chooseInt (0, size - 1) ) $ \j ->
                swapCommutativeProperty array i j


--------------------------------------------------------------------------------
--
--                      Tests for the split function.
--
-- TODO: Missing performance and property tests.
--------------------------------------------------------------------------------
testSplit :: TestTree
testSplit = testGroup "Test Split" [ caseTests ] where

  -- The case tests for the split function.
  caseTests :: TestTree
  caseTests = testGroup "Split Case Tests" [
-- TODO: the below should work for mutable backends too
#ifndef MUTABLE_ARRAYS
      testSplitMid
    ,
#endif
      testSplitEmpty
    ] where

    -- Testing after splitting an array in the middle the sizes of the left and right are correct.
    -- and the contents of the left and right don't change.
    -- Hardcoded array size and values.
    testSplitMid :: TestTree
    testSplitMid = testCase "Test Split Mid" $ do
      let arr = CustomArray.makeArray 6 (1 :: Int)
      let (leftArr, rightArr) = CustomOperations.splitMid arr
      assertEqual "Left array size should be 3" 3 (CustomArray.size leftArr)
      assertEqual "Right array size should be 3" 3 (CustomArray.size rightArr)
      forM_ [0..2] $ \i ->
        assertEqual ("Element at index " ++ show i ++ " in left array") 1 (CustomArray.get leftArr i)
      forM_ [0..2] $ \i ->
        assertEqual ("Element at index " ++ show i ++ " in right array") 1 (CustomArray.get rightArr i)

    -- Tests that splitting an empty array leads to two arrays of size 0.
    testSplitEmpty :: TestTree
    testSplitEmpty = testCase "Test Splitting Empty Array" $ do
      let arr = CustomArray.makeArray 0 (0 :: Int)
      let (leftArr, rightArr) = CustomOperations.splitMid arr
      assertEqual "Left array size should be 0" 0 (CustomArray.size leftArr)
      assertEqual "Right array size should be 0" 0 (CustomArray.size rightArr)
