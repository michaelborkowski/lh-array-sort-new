import Test.Tasty

import ArrayTests
import SortTests
--------------------------------------------------------------------------------

main = defaultMain tests

-- Run tests with "cabal run tests --flag=-liquid-checks".
tests :: TestTree
tests = testGroup "Tests" [ arrayTests, sortTests ]
