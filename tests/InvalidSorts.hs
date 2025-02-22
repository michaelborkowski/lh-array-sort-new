module InvalidSorts (module InvalidSorts) where

import qualified Test.Tasty.QuickCheck as QC

import           Data.List (sort)
--------------------------------------------------------------------------------

-- Function to sort and increment the first element.
incrementFirstElement :: [Int] -> [Int]
incrementFirstElement xs =
  case sorted of
    [] -> []
    _  -> Prelude.take index sorted ++ [sorted !! index + 1] ++ Prelude.drop (index + 1) sorted
  where
    sorted = sort xs
    index = 0

-- Function to sort and increment the middle element.
incrementMiddleElement :: [Int] -> [Int]
incrementMiddleElement xs =
  case sorted of
    [] -> []
    _  -> Prelude.take index sorted ++ [sorted !! index + 1] ++ Prelude.drop (index + 1) sorted
  where
    sorted = sort xs
    index = length sorted `div` 2

-- Function to sort and increment the last element.
incrementLastElement :: [Int] -> [Int]
incrementLastElement xs =
  case sorted of
    [] -> []
    _  -> Prelude.take index sorted ++ [sorted !! index + 1] ++ Prelude.drop (index + 1) sorted
  where
    sorted = sort xs
    index = length sorted - 1

-- Function to sort and remove an element.
removeElement :: [Int] -> [Int]
removeElement xs =
  case sorted of
    [] -> []
    _  -> Prelude.take idx sorted ++ Prelude.drop (idx + 1) sorted
  where
    sorted = sort xs
    idx = length sorted `div` 2

-- Function to sort and add a new element.
addElement :: [Int] -> [Int]
addElement xs =
  let sorted = sort xs
  in sorted ++ [42]

-- Function to sort and displace an element.
displaceElement :: [Int] -> [Int]
displaceElement xs =
  case sorted of
    [] -> []
    [x] -> [x]
    (x:y:zs) -> y : x : zs
  where
    sorted = sort xs