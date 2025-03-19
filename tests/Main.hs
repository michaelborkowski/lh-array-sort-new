import Test.Tasty ( TestTree, defaultMain, testGroup )

import ArrayTests
import SortTests

import           Test.Tasty
import qualified Test.Tasty.QuickCheck as QC
import qualified Array as CustomArray
import           QuickSort (quickSort)
import Test.Tasty.Runners (FailureReason(TestThrewException))
import Debug.Trace (trace)
--------------------------------------------------------------------------------

main = defaultMain tests

-- Run tests on the pure arrays backend with "cabal run tests --flag=-liquid-checks".
-- Run tests on the mutable arrays backend with "cabal run tests -fmutable-arrays".
-- Run tests on the primitive mutable arrays backend with "cabal run tests -fprim-mutable-arrays".
tests :: TestTree
tests = testGroup "Tests"
  [ arrayTests
  , sortTests
  ] where
