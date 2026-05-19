{-# LANGUAGE MonoLocalBinds #-}

module Infra (module Infra) where

import           Test.Tasty
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
import           System.IO.Unsafe (unsafePerformIO)
import           Linear.Common
import           Data.List (sort)
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
--HELPER FUNCTIONS
--------------------------------------------------------------------------------

instance (QC.Arbitrary a, CustomArray.HasPrim a, Random a) => QC.Arbitrary (CustomArray.Array a) where
    arbitrary = do
        size <- QC.chooseInt (1, 1000)  -- hardcode as needed. fromList is not defined for size 0.
        elements <- QC.vectorOf size QC.arbitrary
        return $ CustomArray.fromList elements


-- Runtime parameter to control conditional printing.
verboseTests :: Bool
verboseTests = unsafePerformIO (pure False)  -- Change to `True` for verbose output

-- Helper function to conditionally print.
conditionalPrint :: String -> IO ()
conditionalPrint msg = if verboseTests then putStrLn msg else return ()

-- Prints an array.
printCustomArray :: (CustomArray.HasPrim a, Show a) => CustomArray.Array a -> IO ()
printCustomArray arr = mapM_ print (CustomArray.toList arr)

-- Makes a standard library array of n elements initialized to value v.
makeStandardArray :: Int -> a -> StandardArray.Array Int a
makeStandardArray n v = StandardArray.array (0, n - 1) [(i, v) | i <- [0..n-1]]

-- Print success message.
-- Not recommended to use to avoid clutter in test output.
printSuccess :: String -> IO ()
printSuccess msg = putStrLn ("Success: " ++ msg) >> return ()

-- Utility function for testing exceptions.
assertThrows :: String -> IO a -> (SomeException -> Bool) -> Assertion
assertThrows msg action matcher = do
  result <- try action
  case result of
    Left ex -> assertBool msg (matcher ex)
    Right _ -> assertFailure $ msg ++ ": No exception thrown"


--------------------------------------------------------------------------------
--TEST FUNCTIONS
--------------------------------------------------------------------------------

-- Function to test that swapping two indices in an array properly changes their values.
valueSwapTest :: (CustomArray.HasPrim a, Eq a, Show a)
  => Int
  -- ^ Size of array
  -> a 
  -- ^ The element the array is initialized with
  -> Int 
  -- ^ Index of one element to swap
  -> a 
  -- ^ The initial value to put at index1 (index1)
  -> Int 
  -- ^ Index of the other element to swap (index2)
  -> a 
  -- ^ The initial value to put at index2
  -> TestTree
valueSwapTest size default_element index1 element1 index2 element2 = testCase "Test Values Swapped Generated" $ do
  assertEqual ("index1 should be less than size") (index1 < size) True
  assertEqual ("index2 should be less than size") (index2 < size) True
  let arr = CustomArray.makeArray size default_element
  let arr1 = CustomArray.set arr index1 element1
  let arr2 = CustomArray.set arr1 index2 element2
  let swappedArr = CustomOperations.swap arr2 index1 index2
  assertEqual ("First element should be " ++ show element2) element2 (CustomArray.get swappedArr index1)
  assertEqual ("Second element should be " ++ show element1) element1 (CustomArray.get swappedArr index2)


-- Function for testing that calling something with invalid arguments fails.
-- If the call times out or throws an exception, the test succeeds.
-- If the function returns normally, the test fails.
-- This test is specialized for functions with 2 parameters.
checkInvalid2 :: (Show a, Show b, Show c, Control.DeepSeq.NFData c) => String -> Int -> (a -> b -> c) -> a -> b -> TestTree
checkInvalid2 name timeoutMilliseconds func param1 param2 = testCase name $ do
  result <- timeout (timeoutMilliseconds * 1000) $ do
    (evaluate (func param1 param2) >>= \value -> value `deepseq` pure (Right value))
      `catch` (\ex -> pure (Left (ex :: SomeException)))

  case result of
    Nothing -> conditionalPrint "Timed out" >> return ()
    Just (Left ex) -> conditionalPrint ("Exception - " ++ show ex) >> return ()
    Just (Right val) -> conditionalPrint ("Terminated with value " ++ show val) >> assertFailure "Function terminated successfully but should have failed"

-- Function for testing that calling something with invalid arguments fails.
-- If the call times out or throws an exception, the test succeeds.
-- If the function returns normally, the test fails.
-- This test is specialized for functions with 3 parameters.
checkInvalid3 :: (Show a, Show b, Show c, Show d, Control.DeepSeq.NFData d) => String -> Int -> (a -> b -> c -> d) -> a -> b -> c -> TestTree
checkInvalid3 name timeoutMilliseconds func param1 param2 param3 = testCase name $ do
  result <- timeout (timeoutMilliseconds * 1000) $ do
    (evaluate (func param1 param2 param3) >>= \value -> value `deepseq` pure (Right value))
      `catch` (\ex -> pure (Left (ex :: SomeException)))

  case result of
    Nothing -> conditionalPrint "Timed out" >> return ()
    Just (Left ex) -> conditionalPrint ("Exception - " ++ show ex) >> return ()
    Just (Right val) -> conditionalPrint ("Terminated with value " ++ show val) >> assertFailure "Function terminated successfully but should have failed"

