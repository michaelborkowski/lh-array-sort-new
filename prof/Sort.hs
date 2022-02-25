{-# LANGUAGE BangPatterns #-}

module Sort (isort1, isort2) where

import qualified Array as A

import           Prelude
import qualified Data.Vector.Unboxed as V

--------------------------------------------------------------------------------

insert :: A.ArrayElt a => A.Array a -> a -> Int -> A.Array a
insert xs x 0 =  A.set xs 0 x -- first element is sorted
insert xs x n                 -- sort the nth element into the first n+1 elements
  | x < (A.get xs (n-1)) = insert (A.set xs (n) (A.get xs (n-1))) x (n - 1)
  | otherwise            = A.set xs n x

isort :: A.ArrayElt a => A.Array a -> Int -> A.Array a
isort xs n
  | (A.size xs == 0) = xs
  | (A.size xs == 1) = xs
  -- TODO(ckoparkar): move this allocation out of the recursion
  | (n == 0)       = A.make (A.size xs) (A.get xs 0)
  | otherwise      = insert (isort xs (n-1)) (A.get xs n) n

isort1 :: A.ArrayElt a => A.Array a -> A.Array a
isort1 xs = isort xs (A.size xs - 1)

--------------------------------------------------------------------------------

isort2 :: A.ArrayElt a => A.Array a -> A.Array a
isort2 xs = go 1 (copy xs)
  where
    !n = A.size xs
    copy xs = xs
    go i ys =
      if i == n
      then ys
      else go (i+1) (shift i ys)

    -- shift j ys@(A.Arr ls s e) =
    shift !j ys =
      if j == 0
      -- then (A.Arr ls s e)
      then ys
      else let a = A.get ys j
               b = A.get ys (j-1)
           in if a > b
              -- then (A.Arr ls s e)
              then ys
              else let ys' = A.set (A.set ys j b) (j-1) a
                   in shift (j-1) ys'
