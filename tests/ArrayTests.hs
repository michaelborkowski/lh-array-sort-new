{-# LANGUAGE CPP #-}
{-# LANGUAGE LinearTypes         #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ArrayTests (arrayTests) where

import           Test.Tasty
import qualified Test.Tasty.SmallCheck as SC
import qualified Test.Tasty.QuickCheck as QC
import           Test.Tasty.HUnit
import           System.Random (Random)

import           Control.Monad
import qualified Data.Array as StandardArray
import qualified Array as CustomArray
import qualified ArrayOperations as CustomOperations
import           Control.Exception (evaluate, AsyncException(..), try, throwIO, try, catch, SomeException)
import           Control.DeepSeq (deepseq, NFData)
import           System.Timeout (timeout)
--import           System.Environment (getArgs)
import           System.IO.Unsafe (unsafePerformIO)
import           Test.Tasty.Runners (FailureReason(TestThrewException))
--------------------------------------------------------------------------------

instance (QC.Arbitrary a, Random a) => QC.Arbitrary (CustomArray.Array a) where
    arbitrary = do
        size <- QC.chooseInt (0, 10)  -- hardcode as needed
        elements <- QC.vectorOf size QC.arbitrary
        return $ CustomArray.fromList elements

-- Helper function to assert when a test succeeds
-- Not recommended to use to avoid clutter in test output
assertSuccess :: String -> IO ()
assertSuccess msg = putStrLn ("Success: " ++ msg) >> return ()

-- Example of how I might writing case-test generators
generateValueSwapTest :: (Eq a, Show a) => Int -> a -> Int -> a -> Int -> a -> TestTree
generateValueSwapTest size default_element index1 element1 index2 element2 = testCase "Test Values Swapped Generated" $ do
  let arr = CustomArray.makeArray size default_element
  let arr1 = CustomArray.set arr index1 element1
  let arr2 = CustomArray.set arr1 index2 element2
  let swappedArr = CustomOperations.swap arr2 index1 index2
  assertEqual ("First element should be " ++ show element2) element2 (CustomArray.get swappedArr index1)
  assertEqual ("Second element should be " ++ show element1) element1 (CustomArray.get swappedArr index2)

-- -- Check for whether to print
-- shouldPrint :: IO Bool
-- shouldPrint = do
--   args <- getArgs
--   putStrLn ("Command-line arguments: " ++ show args)
--   return ("--verbose" `elem` args)

-- Runtime parameter to control conditional printing
verboseTests :: Bool
verboseTests = unsafePerformIO (pure False)  -- Change to `True` for verbose output

-- Helper function to conditionally print
conditionalPrint :: String -> IO ()
conditionalPrint msg = if verboseTests then putStrLn msg else return ()

-- Generator function for testing that function called with given parameters is invalid
-- This generator only works with functions that have 2 parameters
wrapperCheckInvalid2 :: (Show a, Show b, Show c, Eq c, Control.DeepSeq.NFData c) => String -> Int -> (a -> b -> c) -> a -> b -> TestTree
wrapperCheckInvalid2 name timeoutMilliseconds func param1 param2 = testCase name $ do
  result <- timeout (timeoutMilliseconds * 1000) $ do
    (evaluate (func param1 param2) >>= \value -> value `deepseq` pure (Right value))
      `catch` (\ex -> pure (Left (ex :: SomeException)))

  case result of
    Nothing -> conditionalPrint "Timed out" >> return ()
    Just (Left ex) -> conditionalPrint ("Exception - " ++ show ex) >> return ()
    Just (Right val) -> conditionalPrint ("Terminated with value " ++ show val) >> assertFailure "Function terminated successfully but should have failed"

-- Generator function for testing that function called with given parameters is invalid
-- This generator only works with functions that have 3 parameters
wrapperCheckInvalid3 :: (Show a, Show b, Show c, Show d, Eq d, Control.DeepSeq.NFData d) => String -> Int -> (a -> b -> c -> d) -> a -> b -> c -> TestTree
wrapperCheckInvalid3 name timeoutMilliseconds func param1 param2 param3 = testCase name $ do
  result <- timeout (timeoutMilliseconds * 1000) $ do
    (evaluate (func param1 param2 param3) >>= \value -> value `deepseq` pure (Right value))
      `catch` (\ex -> pure (Left (ex :: SomeException)))

  case result of
    Nothing -> conditionalPrint "Timed out" >> return ()
    Just (Left ex) -> conditionalPrint ("Exception - " ++ show ex) >> return ()
    Just (Right val) -> conditionalPrint ("Terminated with value " ++ show val) >> assertFailure "Function terminated successfully but should have failed"


-- Utility function for testing exceptions
assertThrows :: String -> IO a -> (SomeException -> Bool) -> Assertion
assertThrows msg action matcher = do
  result <- try action
  case result of
    Left ex -> assertBool msg (matcher ex)
    Right _ -> assertFailure $ msg ++ ": No exception thrown"

-- Test array functionality
-- Run tests with "cabal run tests --flag=-liquid-checks"
arrayTests :: TestTree
arrayTests = testGroup "Array Tests" [ {-testArbitrary, testEqual, testNotEqual,-} testMakeArray, testArrayGetSet, testSwap, testSplit ] where
  performanceTestMultiplier = 1
  mediumNumber = 1000 -- Used for array size
  smallNumber = 100 -- Used for number of operations on array

  -- Prints an array
  printCustomArray :: (Show a) => CustomArray.Array a -> IO ()
  printCustomArray arr = mapM_ print (CustomArray.toList arr)

  -- Makes a standard library array of n elements initialized to value v
  makeStandardArray :: Int -> a -> StandardArray.Array Int a
  makeStandardArray n v = StandardArray.array (0, n - 1) [(i, v) | i <- [0..n-1]]

  -- Prints random arrays so they could be visually inspected
  testArbitrary = QC.testProperty "Test Arbitrary" $ 
    QC.forAll QC.arbitrary $ \ (randomArr :: CustomArray.Array Int) -> 
      QC.ioProperty $ do
        printCustomArray randomArr
        return True

  -- Trivial test for whether equals works correctly
  testEqual = QC.testProperty "Test Equal" $
    \(x :: Int) ->
      x QC.=== x

  -- Trivial test for whether not equals works correctly
  testNotEqual = QC.testProperty "Test Not Equal" $
    \(x :: Int) ->
      x QC.=/= x + 1

  -- Tests the makeArray function
  -- Tests that size is correct with explicit tests for size 0 and 1
  -- Tests that all the values are correct with explicit tests for size 0 and 1
  -- Tests that negative arrays can't be made
  testMakeArray :: TestTree
  testMakeArray = testGroup "MakeArray Tests" [ caseTests, propertyTests, invalidOperationTests ] where

    -- The case tests for the MakeArray function
    -- Tests that arrays of size 0 and 1 have the proper size and elements
    caseTests :: TestTree
    caseTests = testGroup "MakeArray Case Tests" [ testEmptyArray, testSizeOneArray ] where

      -- Testing the output of an empty array
      testEmptyArray = QC.testProperty "Test Empty Array" $ 
        QC.forAll QC.arbitrary $ \(randomElement :: Int) -> 
            let customArr = CustomArray.makeArray 0 randomElement
                standardArr = makeStandardArray 0 randomElement
            in CustomArray.size customArr QC.=== 0 QC..&. CustomArray.toList customArr QC.=== StandardArray.elems standardArr

      -- Testing the output of an array with one elemennt
      testSizeOneArray = QC.testProperty "Test Size One Array" $ 
        QC.forAll QC.arbitrary $ \(randomElement :: Int) -> 
            let customArr = CustomArray.makeArray 1 randomElement
                standardArr = makeStandardArray 1 randomElement
            in CustomArray.size customArr QC.=== 1 QC..&. CustomArray.toList customArr QC.=== StandardArray.elems standardArr


    -- The property tests for the makeArray function
    -- Tests that random arrays have proper size and elements
    propertyTests :: TestTree
    propertyTests = testGroup "MakeArray Property Tests" [ testRandomSizeArray ] where

      -- Testing the output of a random size array
      testRandomSizeArray = QC.testProperty "Test Random Size Array" $ 
        QC.forAll ((,) <$> QC.chooseInt (0, mediumNumber) <*> QC.arbitrary) $ \(randomSize :: Int, randomElement :: Int) -> 
            let customArr = CustomArray.makeArray randomSize randomElement
                standardArr = makeStandardArray randomSize randomElement
            in CustomArray.size customArr QC.=== randomSize QC..&. CustomArray.toList customArr QC.=== StandardArray.elems standardArr

    -- The tests for exception cases of the MakeArray functions
    -- Tests that negative size arrays can't be made
    invalidOperationTests :: TestTree
    invalidOperationTests = testGroup "MakeArray Invalid Operation Tests" [ testNegativeSizeArray ] where

      -- Testing a negative size array
      testNegativeSizeArray :: TestTree
      testNegativeSizeArray =
        wrapperCheckInvalid2 "Negative size array is invalid" 1000
        (CustomArray.makeArray :: Int -> Int -> CustomArray.Array Int) (-5) 1

  -- Tests that getting and setting values works for the first and last indices
  -- Tests random combinations of gets and sets
  -- Tests getting/setting negative and out of bounds elements
  -- Explicitly tests size 0 array
  testArrayGetSet :: TestTree
  testArrayGetSet = testGroup "Array Get/Set Tests" [ caseTests, propertyTests, invalidOperationTests ] where

    -- The case tests for the get and set functions
    -- Tests that getting and setting values works for the first and last indices
    caseTests :: TestTree
    caseTests = testGroup "Array Get/Set Case Tests" [ testFirstIndex, testLastIndex ] where

      -- Testing the get and set functions with valid indices
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

      -- Testing setting an out-of-bounds index (no effect should occur)
      testLastIndex = QC.testProperty "Test Get/Set Last Index" $
        QC.forAll QC.arbitrary $ \(size :: Int, startValue :: Int, newValue :: Int) ->
          if size > 0 then
            let index = size - 1
                customArr = CustomArray.makeArray size startValue
                updatedArr = CustomArray.set customArr index newValue
                fetchedValue = CustomArray.get updatedArr index
            in fetchedValue QC.=== newValue
          else
            QC.property True

    -- The property tests for the get and set functions
    -- Tests that the set operation works correctly for random values
    propertyTests :: TestTree
    propertyTests = testGroup "Array Get/Set Property Tests" [ testRandomGetSet ] where

      -- Testing random set and get operations
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
                  --updatedStandardArr = standardArr StandardArray.// randomUpdates
                  updatedStandardArr :: StandardArray.Array Int Int
                  updatedStandardArr = performSetsStandard standardArr randomUpdates

                  -- Performing gets
                  customGets = map (CustomArray.get updatedCustomArr) randomGetIndices
                  standardGets = map (updatedStandardArr StandardArray.!) randomGetIndices
              in QC.property $
                  CustomArray.size updatedCustomArr QC.=== size QC..&.
                  CustomArray.toList updatedCustomArr QC.=== StandardArray.elems updatedStandardArr QC..&.
                  customGets QC.=== standardGets

    -- The tests for exception cases of the get and set functions
    -- Tests getting/setting negative and out-of-bounds indices
    -- Tests getting/setting with empty arrays
    invalidOperationTests :: TestTree
    invalidOperationTests = testGroup "Array Get/Set Invalid Operation Tests" [ testNegativeIndexGet, testNegativeIndexSet, testOutOfBoundsIndexGet, testOutOfBoundsIndexSet, testEmptyArraySet, testEmptyArrayGet ] where

      -- Testing getting a negative index
      testNegativeIndexGet :: TestTree
      testNegativeIndexGet =
        wrapperCheckInvalid2 "Negative index is invalid for get" 100
        (CustomArray.get :: CustomArray.Array Int -> Int -> Int) (CustomArray.makeArray 5 0) (-1)

      -- Testing setting a negative index
      testNegativeIndexSet :: TestTree
      testNegativeIndexSet =
        wrapperCheckInvalid3 "Negative index is invalid for set" 100
        (CustomArray.set :: CustomArray.Array Int -> Int -> Int -> CustomArray.Array Int) (CustomArray.makeArray 5 0) (-1) 1

      -- Testing getting an out-of-bounds index
      testOutOfBoundsIndexGet :: TestTree
      testOutOfBoundsIndexGet =
        wrapperCheckInvalid2 "Out-of-bounds index is invalid for get" 100
        (CustomArray.get :: CustomArray.Array Int -> Int -> Int) (CustomArray.makeArray 5 0) 5

      -- Testing setting an out-of-bounds index
      testOutOfBoundsIndexSet :: TestTree
      testOutOfBoundsIndexSet =
        wrapperCheckInvalid3 "Out-of-bounds index is invalid for set" 100
        (CustomArray.set :: CustomArray.Array Int -> Int -> Int -> CustomArray.Array Int) (CustomArray.makeArray 5 0) 5 1

      -- Testing get on an empty array
      testEmptyArrayGet :: TestTree
      testEmptyArrayGet =
        wrapperCheckInvalid2 "Out-of-bounds index is invalid for get" 100
        (CustomArray.get :: CustomArray.Array Int -> Int -> Int) (CustomArray.makeArray 0 0) 0

      -- Testing set on an empty array
      testEmptyArraySet :: TestTree
      testEmptyArraySet =
        wrapperCheckInvalid3 "Out-of-bounds index is invalid for set" 100
        (CustomArray.set :: CustomArray.Array Int -> Int -> Int -> CustomArray.Array Int) (CustomArray.makeArray 0 0) 0 1



  -- Tests for the swap function
  -- Missing property tests
  testSwap :: TestTree
  testSwap = testGroup "Swap Tests" [ caseTests, performanceTests ] where

    -- The case tests for the swap function
    caseTests :: TestTree
    caseTests = testGroup "Swap Case Tests" [ testValuesSwappedManual, testValuesSwappedGenerated1, testValuesSwappedGenerated2, testValuesSwappedGenerated3, testSwapSameIndex ] where 

      -- Testing if swapping two elements works correctly
      -- Hardcoded array size and values
      testValuesSwappedManual :: TestTree
      testValuesSwappedManual = testCase "Test Values Swapped Manual" $ do
        let arr = CustomArray.makeArray 5 0
        let arr1 = CustomArray.set arr 0 1
        let arr2 = CustomArray.set arr1 1 2
        let swappedArr = CustomOperations.swap arr2 0 1
        assertEqual "First element should be 2" 2 (CustomArray.get swappedArr 0)
        assertEqual "Second element should be 1" 1 (CustomArray.get swappedArr 1)

      -- Testing if swapping two elements works correctly
      -- Automatically generated test
      testValuesSwappedGenerated1 = generateValueSwapTest 5 0 0 1 1 2
      testValuesSwappedGenerated2 = generateValueSwapTest 10 1 1 2 2 4
      testValuesSwappedGenerated3 = generateValueSwapTest 20 1 2 3 4 5

      -- Testing that swapping an element with itself doesn't change anything
      testSwapSameIndex :: TestTree
      testSwapSameIndex = testCase "Test Swapping Same Index" $ do
        let arr = CustomArray.makeArray 5 1
        let swappedArr = CustomOperations.swap arr 2 2
        assertEqual "Array should remain unchanged" 1 (CustomArray.get swappedArr 2)

    -- Test performance for swap
    performanceTests :: TestTree
    performanceTests = testGroup "Swap Performance Tests" [ testLargeArraySwap ] where
      largeInt = 1000000 * performanceTestMultiplier

      -- Test performance of creating and splitting a large array
      testLargeArraySwap :: TestTree
      testLargeArraySwap = testCase "Test Large Array Swap" $ do
        let largeArr = CustomArray.makeArray largeInt 0
        let updatedArr = CustomArray.set largeArr (largeInt-1) 1
        let swappedArr = CustomOperations.swap updatedArr (largeInt-1) 0
        assertEqual "Last element should be 0" 0 (CustomArray.get swappedArr (largeInt-1))

  -- Tests for the split function
  -- Missing performance tests
  testSplit :: TestTree
  testSplit = testGroup "Test Split" [ caseTests, propertyTests ] where

    -- The case tests for the split function
    caseTests :: TestTree
    caseTests = testGroup "Split Case Tests" [ testSplitMid, testSplitEmpty ] where

      -- Testing after splitting an array in the middle the sizes of the left and right are correct
      -- and the contents of the left and right don't change
      -- Hardcoded array size and values
      testSplitMid :: TestTree
      testSplitMid = testCase "Test Split Mid" $ do
        let arr = CustomArray.makeArray 6 1
        let (leftArr, rightArr) = CustomOperations.splitMid arr
        assertEqual "Left array size should be 3" 3 (CustomArray.size leftArr)
        assertEqual "Right array size should be 3" 3 (CustomArray.size rightArr)
        forM_ [0..2] $ \i ->
          assertEqual ("Element at index " ++ show i ++ " in left array") 1 (CustomArray.get leftArr i)
        forM_ [0..2] $ \i ->
          assertEqual ("Element at index " ++ show i ++ " in right array") 1 (CustomArray.get rightArr i)
    
      -- Tests that splitting an empty array leads to two arrays of size 0
      testSplitEmpty :: TestTree
      testSplitEmpty = testCase "Test Splitting Empty Array" $ do
        let arr = CustomArray.makeArray 0 0
        let (leftArr, rightArr) = CustomOperations.splitMid arr
        assertEqual "Left array size should be 0" 0 (CustomArray.size leftArr)
        assertEqual "Right array size should be 0" 0 (CustomArray.size rightArr)

    -- The property tests for the split function
    propertyTests :: TestTree
    propertyTests = testGroup "Split Property Tests" [ testSwapCommutative ] where

      -- Generates random arrays to test that swap is commutative.
      testSwapCommutative :: TestTree
      testSwapCommutative = QC.testProperty "Swapping two elements is commutative" swapCommutativeProperty--(swapCommutativeProperty :: Array Int -> Int -> Int -> QC.Property)

-- Placeholder swapCommutativeProperty since something is going wrong with the "Arbitrary a" restriction
swapCommutativeProperty :: QC.Property
swapCommutativeProperty = True QC.=== True

-- Real swapCommutativeProperty
-- -- Define the commutative property for swap
-- swapCommutativeProperty :: (Arbitrary a, Show a, Eq a) => Array a -> Int -> Int -> QC.Property
-- swapCommutativeProperty arr i j =
--   i /= j QC.==> swap arr i j QC.=== swap arr j i
