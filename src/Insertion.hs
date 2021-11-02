{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}
-- {-@ LIQUID "--checks=lma_insert_eq" @-}


-- {-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Insertion where

import           Prelude hiding ((++)) 
import           ProofCombinators
-- import qualified State as S
import qualified Data.Set as S
-- import           Expressions 
import           Imp  
import           BigStep
import           Array
import           Order
import           Equivalence



--------------------------------------------------------------------------------
-- | Implementations
--------------------------------------------------------------------------------

-- input xs needs to have one extra space at the end. 
{-@ reflect insert @-}
{-@ insert :: xs:_ -> x:_ -> n:{v:Nat | v < size xs}
       -> ys:{size ys == size xs} / [n] @-}

insert :: Ord a => Array a -> a -> Int -> Array a
insert xs x 0 =  set xs 0 x -- first element is sorted
insert xs x n               -- sort the nth element into the first n+1 elements
  | x < (get xs (n-1)) = insert (set xs (n) (get xs (n-1))) x (n - 1)
  | otherwise          = set xs n x

-- >>>  isort (fromList [1,3,2,9,6,0,5,2,10,-1]) 9
{-@ reflect isort @-}
{-@ isort :: xs:_ -> n:{v:Nat | v < size xs}
      -> ys:{size ys == size xs} / [n] @-}
isort :: Ord a => Array a -> Int -> Array a
isort xs n 
  | (size xs == 0) = xs
  | (size xs == 1) = xs
  | (n == 0)       = make (size xs) (get xs 0)
  | otherwise      = insert (isort xs (n-1)) (get xs n) n


--------------------------------------------------------------------------------
-- | Proofs for Sortedness
--------------------------------------------------------------------------------

-- lemma that shows insert on first n does not affect the elements after n
{-@ lma_insert_fix :: xs:_ -> x:_ -> n:{v:Nat | v < size xs} -> m:{v:Nat | v > n && v < size xs}
      -> ys:{get (insert xs x n) m == get xs m} / [n] @-}
lma_insert_fix :: Ord a => Array a -> a -> Int -> Int -> Proof
lma_insert_fix xs x 0 m = ()
lma_insert_fix xs x n m
  | x < (get xs (n-1)) 
    = get (insert xs x n) m
    -- === get (insert (set xs (n) (get xs (n-1))) x (n - 1)) m
      ? (lma_insert_fix (set xs (n) (get xs (n-1))) x (n-1) m)
    -- === get (set xs (n) (get xs (n-1))) m
      ? (lma_gns xs n m (get xs (n-1)))
    === get xs m
    *** QED
  | otherwise
    = get (insert xs x n) m 
    -- === get (set xs n x) m 
      ? (lma_gns xs n m x)
    === get xs m
    *** QED


-- more general lemma would be to show that the last index of (insert xs x n) 
-- is either x or last of xs, but this form is handy in our case
{-@ lma_insert_max :: xs:_ -> x:_ -> y:_ -> n:{v:Nat | (v < size xs) && (v > 0) && (x <= y) && ((get xs (n-1)) <= y)}
      -> ys:{y >= get (insert xs x n) n} / [n] @-}
lma_insert_max :: Ord a => Array a -> a -> a -> Int -> Proof
lma_insert_max xs x y n
  | x < (get xs (n-1)) 
    = y
    =>= get xs (n-1)
      ? (lma_gs xs n (get xs (n-1)))
    -- === get (set xs (n) (get xs (n-1))) n
      ? (lma_insert_fix (set xs (n) (get xs (n-1))) x (n-1) n)
    -- === get (insert (set xs (n) (get xs (n-1))) x (n-1)) n
    === get (insert xs x n) n
    *** QED
  | otherwise
    = y
    =>= x
      ? (lma_gs xs n x)
    -- === get (set xs n x) n
    === get (insert xs x n) n
    *** QED


{-@ lma_insert :: xs:_ -> x:_ -> n:{v:Nat | v < size xs && (isSortedFstN xs (v))}
      -> ys:{isSortedFstN (insert xs x n) (n+1)} / [n] @-}
lma_insert :: Ord a => Array a -> a -> Int -> Proof
lma_insert xs x 0 = ()
lma_insert xs x n 
  | x < (get xs (n-1)) 
    = let 
        xs' = (set xs (n) (get xs (n-1)))
        ys  = (insert xs' x (n-1))
      in isSortedFstN (insert xs x n) (n+1)
        -- === isSortedFstN ys (n+1)
        -- === (((get ys (n-1)) <= (get ys n)) && (isSortedFstN ys n))
          ? (lma_insert xs' x (n-1 ? (lma_isfn_set xs (get xs (n-1)) n (n-1))))  
        -- === (get ys (n-1)) <= (get ys (n))
          ? (lma_insert_fix xs' x (n-1) n)
        -- === (get ys (n-1)) <= (get xs' (n)) 
          ? (lma_gs xs n (get xs (n-1)))
        -- === (get ys (n-1)) <= (get xs (n-1)) 
          ? (if (n >= 2) 
            then (lma_insert_max xs' x (get xs (n-1)) (n-1 ? (lma_gns xs n (n-2) (get xs (n-1))))) 
            else (lma_gs xs 0 x))
        === True
        *** QED
  | otherwise
    = let 
        xs' = (set xs n x)
        -- ys  = (insert xs' x (n-1))
      in isSortedFstN (insert xs x n) (n+1)
        -- === isSortedFstN xs' (n+1)
        -- === (((get xs' (n-1)) <= (get xs' n)) && (isSortedFstN xs' n))
          ? (lma_isfn_set xs x n n)
        -- === (((get xs' (n-1)) <= (get xs' n)) && (isSortedFstN xs n))
        -- === ((get xs' (n-1)) <= (get xs' n)) 
          ? (lma_gns xs n (n-1) x) &&& (lma_gs xs n x)
        -- === ((get xs (n-1)) <= x) 
        === True
        *** QED


{-@ lma_isort :: xs:_ -> n:{v:Nat | v < size xs }
      -> ys:{isSortedFstN (isort xs n) (n+1)} / [n] @-}
lma_isort :: Ord a => Array a -> Int -> Proof
lma_isort xs n 
  | (size xs == 0) = ()
  | (size xs == 1) = ()
  | (n == 0)       = ()
  | otherwise
    = isSortedFstN (isort xs n) (n+1)
    -- === isSortedFstN (insert (isort xs (n-1)) (get xs n) n) (n+1)
      ? (lma_insert (isort xs (n-1)) (get xs n) (n ? (lma_isort xs (n-1))))
    === True
    *** QED


--------------------------------------------------------------------------------
-- | Proofs for Equivalence
--------------------------------------------------------------------------------

-- TODO: will be nice if there is an option to enable showing the constrains LH is checking during compile time
-- LH Checking involving Sets are very slow
{-@ lma_insert_eq :: xs:_ -> x:_ -> n:{v:Nat | v < size xs}
       -> ys:{(toSet (insert xs x n) (n+1)) == (S.union (S.singleton x) (toSet xs n))} / [n] @-} 
lma_insert_eq :: Ord a => Array a -> a -> Int -> Proof
lma_insert_eq xs x 0 = ()
lma_insert_eq xs x n
  | x < (get xs (n-1)) 
    = let 
        xs' = (set xs (n) (get xs (n-1)))
        ys = (insert xs' x (n - 1))
      in toSet (insert xs x n) (n+1)
      -- === toSet ys (n+1)
      -- === S.union (S.singleton (get ys n)) (toSet ys n)
        ? (lma_insert_eq xs' x (n-1))
      -- === S.union (S.singleton (get ys n)) (S.union (S.singleton x) (toSet xs' (n-1)))
      -- === S.union (S.singleton x) (S.union (S.singleton (get ys n)) (toSet xs' (n-1)))
        ? (lma_set_equal xs (get xs (n-1)) n (n-1))
      -- === S.union (S.singleton x) (S.union (S.singleton (get ys n)) (toSet xs (n-1)))
        ? (lma_insert_fix xs' x (n-1) n)
      -- === S.union (S.singleton x) (S.union (S.singleton (get xs' n)) (toSet xs (n-1)))
        ? (lma_gs xs n (get xs (n-1)))
      -- === S.union (S.singleton x) (S.union (S.singleton (get xs (n-1))) (toSet xs (n-1)))
      === S.union (S.singleton x) (toSet xs n)
      *** QED
  | otherwise
    = toSet (insert xs x n) (n+1)
    -- === toSet (set xs n x) (n+1)
    -- === S.union (S.singleton (get (set xs n x) n)) (toSet (set xs n x) n)
      ? (lma_gs xs n x) &&& (lma_set_equal xs x n n)
    === (S.union (S.singleton x) (toSet xs n))
    *** QED


{-@ lma_isort_eq_r :: xs:_ -> n:{v:Nat | v < size xs}
       -> ys:{toSet (isort xs n) (n+1) == toSet xs (n+1)} / [n] @-} 
lma_isort_eq_r :: Ord a => Array a -> Int -> Proof
lma_isort_eq_r xs n 
  | (size xs == 0) = ()
  | (size xs == 1) = ()
  | (n == 0)       = ()
  | otherwise 
    = toSet (isort xs n) (n+1)
    -- === toSet (insert (isort xs (n-1)) (get xs n) n) (n+1)
      ? (lma_insert_eq (isort xs (n-1)) (get xs n) n)
    -- === S.union (S.singleton (get xs n)) (toSet (isort xs (n-1)) n)
      ? (lma_isort_eq_r xs (n-1))
    -- === S.union (S.singleton (get xs n)) (toSet xs (n))
    === (toSet xs (n+1))
    *** QED


{-@ lma_isort_eq :: xs:_
       -> { equalP (isort xs ((size xs)-1)) xs } @-}
lma_isort_eq :: Ord a => Array a -> Proof
lma_isort_eq xs 
  | (size xs == 0) = ()
  | otherwise      
    = toSet (isort xs ((size xs)-1)) (size (isort xs ((size xs)-1)))
    -- === toSet (isort xs ((size xs)-1)) (size xs)
      ? lma_isort_eq_r xs ((size xs)-1)
    === toSet xs (size xs)
    *** QED
