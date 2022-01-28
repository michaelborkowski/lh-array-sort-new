{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}
-- {-@ LIQUID "--checks=lma_insert_eq" @-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}

module Insertion where

import           Prelude
import           Language.Haskell.Liquid.ProofCombinators
import qualified Language.Haskell.Liquid.Bag as B
import qualified Array as A
import           Order
import           Equivalence


--------------------------------------------------------------------------------
-- | Implementations
--------------------------------------------------------------------------------

-- input xs needs to have one extra space at the end.
{-@ reflect insert @-}
{-@ insert :: xs:_ -> x:_ -> n:{v:Nat | v < A.size xs}
       -> ys:{A.size ys == A.size xs} / [n] @-}

insert :: Ord a => A.Array a -> a -> Int -> A.Array a
insert xs x 0 =  A.set xs 0 x -- first element is sorted
insert xs x n                 -- sort the nth element into the first n+1 elements
  | x < (A.get xs (n-1)) = insert (A.set xs (n) (A.get xs (n-1))) x (n - 1)
  | otherwise            = A.set xs n x

{-@ reflect isort @-}
{-@ isort :: xs:_ -> n:{v:Nat | v < A.size xs}
      -> ys:{A.size ys == A.size xs} / [n] @-}
isort :: Ord a => A.Array a -> Int -> A.Array a
isort xs n
  | (A.size xs == 0) = xs
  | (A.size xs == 1) = xs
  -- TODO(ckoparkar): move this allocation out of the recursion
  | (n == 0)       = A.make (A.size xs) (A.get xs 0)
  | otherwise      = insert (isort xs (n-1)) (A.get xs n) n

isort1 :: Ord a => A.Array a -> A.Array a
isort1 xs = isort xs (A.size xs - 1)


{-|

for (i = 1 ; i <= n - 1; i++) {
    j = i;
    while ( j > 0 && arr[j-1] > arr[j]) {
        temp     = arr[j];
        arr[j]   = arr[j-1];
        arr[j-1] = temp;
        j--;
    }
}

-}
isort2 :: Ord a => A.Array a -> A.Array a
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

--------------------------------------------------------------------------------
-- | Proofs for Sortedness
--------------------------------------------------------------------------------

-- lemma that shows insert on first n does not affect the elements after n
{-@ lma_insert_fix :: xs:_ -> x:_ -> n:{v:Nat | v < A.size xs} -> m:{v:Nat | v > n && v < A.size xs}
      -> ys:{A.get (insert xs x n) m == A.get xs m} / [n] @-}
lma_insert_fix :: Ord a => A.Array a -> a -> Int -> Int -> Proof
lma_insert_fix xs x 0 m
  = A.get (insert xs x 0) m
  -- === A.get (A.set xs 0 x) m
    ? (A.lma_gns xs 0 m x)
  === A.get xs m
  *** QED

lma_insert_fix xs x n m
  | x < (A.get xs (n-1))
    = A.get (insert xs x n) m
    -- === A.get (insert (A.set xs (n) (A.get xs (n-1))) x (n - 1)) m
      ? (lma_insert_fix (A.set xs (n) (A.get xs (n-1))) x (n-1) m)
    -- === A.get (A.set xs (n) (A.get xs (n-1))) m
      ? (A.lma_gns xs n m (A.get xs (n-1)))
    === A.get xs m
    *** QED
  | otherwise
    = A.get (insert xs x n) m
    -- === A.get (A.set xs n x) m
      ? (A.lma_gns xs n m x)
    === A.get xs m
    *** QED

-- more general lemma would be to show that the last index of (insert xs x n)
-- is either x or last of xs, but this form is handy in our case
{-@ lma_insert_max :: xs:_ -> x:_ -> y:_ -> n:{v:Nat | (v < A.size xs) && (v > 0) && (x <= y) && ((A.get xs (n-1)) <= y)}
      -> ys:{y >= A.get (insert xs x n) n} / [n] @-}
lma_insert_max :: Ord a => A.Array a -> a -> a -> Int -> Proof
lma_insert_max xs x y n
  | x < (A.get xs (n-1))
    = y
    =>= A.get xs (n-1)
      ? (A.lma_gs xs n (A.get xs (n-1)))
    -- === A.get (A.set xs (n) (A.get xs (n-1))) n
      ? (lma_insert_fix (A.set xs (n) (A.get xs (n-1))) x (n-1) n)
    -- === A.get (insert (A.set xs (n) (A.get xs (n-1))) x (n-1)) n
    === A.get (insert xs x n) n
    *** QED
  | otherwise
    = y
    =>= x
      ? (A.lma_gs xs n x)
    -- === A.get (A.set xs n x) n
    === A.get (insert xs x n) n
    *** QED

{-@ lma_insert :: xs:_ -> x:_ -> n:{v:Nat | v < A.size xs && (isSortedFstN xs (v))}
      -> ys:{isSortedFstN (insert xs x n) (n+1)} / [n] @-}
lma_insert :: Ord a => A.Array a -> a -> Int -> Proof
lma_insert xs x 0 = ()
lma_insert xs x n
  | x < (A.get xs (n-1)) && (n >= 2)
    = let
        xs' = (A.set xs (n) (A.get xs (n-1)))
        ys  = (insert xs' x (n-1))
      in isSortedFstN (insert xs x n) (n+1)
        -- === isSortedFstN ys (n+1)
        -- === (((A.get ys (n-1)) <= (A.get ys n)) && (isSortedFstN ys n))
          ? (lma_insert xs' x (n-1 ? (lma_isfn_set xs (A.get xs (n-1)) n (n-1))))
        -- === (A.get ys (n-1)) <= (A.get ys (n))
          ? (lma_insert_fix xs' x (n-1) n)
        -- === (A.get ys (n-1)) <= (A.get xs' (n))
          ? (A.lma_gs xs n (A.get xs (n-1)))
        -- === (A.get ys (n-1)) <= (A.get xs (n-1))
          ? (lma_insert_max xs' x (A.get xs (n-1)) (n-1 ? (A.lma_gns xs n (n-2) (A.get xs (n-1)))))
        === True
        *** QED
  | x < (A.get xs (n-1)) && (n < 2)
    = let
        xs' = (A.set xs (n) (A.get xs (n-1)))
        ys  = (insert xs' x (n-1))
      in isSortedFstN (insert xs x n) (n+1)
        -- === isSortedFstN ys (n+1)
        -- === (((A.get ys (n-1)) <= (A.get ys n)) && (isSortedFstN ys n))
          ? (lma_insert xs' x (n-1 ? (lma_isfn_set xs (A.get xs (n-1)) n (n-1))))
        -- === (A.get ys (n-1)) <= (A.get ys (n))
          ? (lma_insert_fix xs' x (n-1) n)
        -- === (A.get ys (n-1)) <= (A.get xs' (n))
          ? (A.lma_gs xs n (A.get xs (n-1)))
        -- === (A.get ys (n-1)) <= (A.get xs (n-1))
          ? (A.lma_gs xs' 0 x)-- A.get ys (n-1) === get (insert xs' x (n-1)) (n-1) ===
        -- === x <= (A.get xs (n-1))
        === True
        *** QED
  | otherwise
    = let
        xs' = (A.set xs n x)
        -- ys  = (insert xs' x (n-1))
      in isSortedFstN (insert xs x n) (n+1)
        -- === isSortedFstN xs' (n+1)
        -- === (((A.get xs' (n-1)) <= (A.get xs' n)) && (isSortedFstN xs' n))
          ? (lma_isfn_set xs x n n)
        -- === (((A.get xs' (n-1)) <= (A.get xs' n)) && (isSortedFstN xs n))
        -- === ((A.get xs' (n-1)) <= (A.get xs' n))
          ? (A.lma_gns xs n (n-1) x) &&& (A.lma_gs xs n x)
        -- === ((A.get xs (n-1)) <= x)
        === True
        *** QED

{-@ lma_isort :: xs:_ -> n:{v:Nat | v < A.size xs }
      -> ys:{isSortedFstN (isort xs n) (n+1)} / [n] @-}
lma_isort :: Ord a => A.Array a -> Int -> Proof
lma_isort xs n
  | (A.size xs == 0) = ()
  | (A.size xs == 1) = ()
  | (n == 0)       = ()
  | otherwise
    = isSortedFstN (isort xs n) (n+1)
    -- === isSortedFstN (insert (isort xs (n-1)) (A.get xs n) n) (n+1)
      ? (lma_insert (isort xs (n-1)) (A.get xs n) (n ? (lma_isort xs (n-1))))
    === True
    *** QED

--------------------------------------------------------------------------------
-- | Proofs for Equivalence
--------------------------------------------------------------------------------

{-@ lma_insert_eq :: xs:_ -> x:_ -> n:{v:Nat | v < A.size xs}
       -> ys:{(toBagLeft (insert xs x n) (n+1)) == (B.put x (toBagLeft xs n))} / [n] @-}
lma_insert_eq :: Ord a => A.Array a -> a -> Int -> Proof
lma_insert_eq xs x 0
  = toBagLeft (insert xs x 0) 1
  -- === toBagLeft (A.set xs 0 x) 1
  -- === B.put (A.get (A.set xs 0 x) 0) (toBagLeft xs 0)
    ? (A.lma_gs xs 0 x)
  === B.put x (toBagLeft xs 0)
  *** QED
lma_insert_eq xs x n
  | x < (A.get xs (n-1))
    = let
        xs' = (A.set xs (n) (A.get xs (n-1)))
        ys = (insert xs' x (n - 1))
      in toBagLeft (insert xs x n) (n+1)
      === toBagLeft ys (n+1)
      -- === B.put (A.get ys n) (toBagLeft ys n)
        ? (lma_insert_eq xs' x (n-1))
      -- === B.put (A.get ys n) (B.put x (toBagLeft xs' (n-1)))
      -- === B.put x (B.put (A.get ys n) (toBagLeft xs' (n-1)))
        ? (lma_set_equal xs (A.get xs (n-1)) n (n-1))
      -- === B.put x (B.put (A.get ys n) (toBagLeft xs (n-1)))
        ? (lma_insert_fix xs' x (n-1) n)
      -- === B.put x (B.put (A.get xs' n) (toBagLeft xs (n-1)))
        ? (A.lma_gs xs n (A.get xs (n-1)))
      -- === B.put x (B.put (A.get xs (n-1)) (toBagLeft xs (n-1)))
      === B.put x (toBagLeft xs n)
      *** QED
  | otherwise
    = toBagLeft (insert xs x n) (n+1)
    -- === toBagLeft (A.set xs n x) (n+1)
    -- === B.put (A.get (A.set xs n x) n) (toBagLeft (A.set xs n x) n)
      ? (A.lma_gs xs n x) &&& (lma_set_equal xs x n n)
    === (B.put x (toBagLeft xs n))
    *** QED

{-@ lma_isort_eq_r :: xs:_ -> n:{v:Nat | v < A.size xs}
       -> ys:{toBagLeft (isort xs n) (n+1) == toBagLeft xs (n+1)} / [n] @-}
lma_isort_eq_r :: Ord a => A.Array a -> Int -> Proof
lma_isort_eq_r xs n
  | (A.size xs == 0) = ()
  | (A.size xs == 1) = ()
  | (n == 0)
    = toBagLeft (isort xs 0) 1
    -- === B.put (A.get (isort xs 0) 0) (toBagLeft (isort xs 0) 0)
    === B.put (A.get (A.make (A.size xs) (A.get xs 0)) 0) (toBagLeft (isort xs 0) 0) -- TODO: UNSAFE if this line gets commented
    -- === B.put (A.get xs 0) (toBagLeft xs 0)
    === toBagLeft xs 1
    *** QED
  | otherwise
    = toBagLeft (isort xs n) (n+1)
    -- === toBagLeft (insert (isort xs (n-1)) (A.get xs n) n) (n+1)
      ? (lma_insert_eq (isort xs (n-1)) (A.get xs n) n)
    -- === B.union (S.singleton (A.get xs n)) (toBagLeft (isort xs (n-1)) n)
      ? (lma_isort_eq_r xs (n-1))
    -- === B.union (S.singleton (A.get xs n)) (toBagLeft xs (n))
    === (toBagLeft xs (n+1))
    *** QED

{-@ lma_isort_eq :: xs:_
       -> { toBagEqual (isort xs ((A.size xs)-1)) xs } @-}
lma_isort_eq :: Ord a => A.Array a -> Proof
lma_isort_eq xs
  | (A.size xs == 0) = ()
  | otherwise
    = toBagLeft (isort xs ((A.size xs)-1)) (A.size (isort xs ((A.size xs)-1)))
    -- === toBagLeft (isort xs ((A.size xs)-1)) (A.size xs)
      ? lma_isort_eq_r xs ((A.size xs)-1)
    === toBagLeft xs (A.size xs)
    *** QED
