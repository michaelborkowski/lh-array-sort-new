{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}


-- {-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Order where

import           Prelude hiding ((++)) 
import           ProofCombinators
import qualified State as S
-- import qualified Data.Set as S
-- import           Expressions 
import           Imp 
import           BigStep
import           Array



data List a = Nil | Cons a (List a)
  deriving (Eq, Show)

-- TODO: List equal up to permutation

{-@ reflect myhead @-}
myhead :: List a -> Maybe a
myhead Nil = Nothing
myhead (Cons x xs) = Just x

{-@ reflect app @-}
app :: List a -> List a -> List a 
app Nil ys         = ys 
app (Cons x xs) ys = Cons x (app xs ys)


-- proofs

-- lemma showing set preserves sortedness of indices before n, and if the new 
-- element is greater than the previous, xs is sorted up to n+1
{-@ lma_set_ps :: xs:_ -> n:{m:Nat | m < size xs && m > 0 } -> x:{(isSortedFstN xs n) && ((x >= (get xs (n-1))))} 
      -> { isSortedFstN (set xs n x) (n+1)} / [n]@-}
lma_set_ps :: Ord a => Array a -> Int -> a -> Proof
lma_set_ps xs 1 x = ()
lma_set_ps xs n x 
  = isSortedFstN (set xs n x) (n+1)
  -- === (((get (set xs n x) (n-1)) <= (get (set xs n x) (n))) && (isSortedFstN (set xs n x) (n)))
    ? (lma_gns xs n (n-1) x) &&& (lma_gs xs n x)
  -- === (((get xs (n-1)) <= x) && (isSortedFstN (set xs n x) (n)))
  -- === (isSortedFstN (set xs n x) (n)) 
  -- === (((get (set xs n x) (n-2)) <= (get (set xs n x) (n-1))) && (isSortedFstN (set xs n x) (n-1)))
    ? (lma_gns xs n (n-2) x) &&& (lma_gns xs n (n-1) x)
  -- === (((get xs (n-2)) <= (get xs (n-1))) && (isSortedFstN (set xs n x) (n-1)))
  -- === isSortedFstN (set xs n x) (n-1)
    ? lma_isfn_set xs x n (n-1)
  -- === isSortedFstN xs (n-1)
  === True
  *** QED


-- subfunctions in measure has to be measure as well? TODO:
{-@ reflect isSorted @-}
isSorted :: Ord a => Array a -> Bool
isSorted xs = isSortedFstN xs (size xs)


{-@ reflect isSortedFstN @-}
{-@ isSortedFstN :: xs:_ -> m:{n:Nat | n <= size xs} -> b:_ / [m] @-}
isSortedFstN :: Ord a => Array a -> Int -> Bool
isSortedFstN xs 0 = True
isSortedFstN xs 1 = True
isSortedFstN xs n = ((get xs (n-2)) <= (get xs (n-1))) && (isSortedFstN xs (n-1))

-- lemma showing that isSorted xs implies isSorted for first n when n in range
{-@ lma_is_isfn :: xs:{isSorted xs} -> n:{v:Nat |  v <= size xs} 
      -> {isSortedFstN xs n} / [n] @-}
lma_is_isfn :: Ord a => Array a -> Int -> Proof
lma_is_isfn xs n 
  = True
  -- === isSorted xs
  -- === isSortedFstN xs (size xs)
    ? lma_isfn1 xs (size xs) n
  === isSortedFstN xs n
  *** QED


-- lemma showing that set xs n x does not change the fact that the first m<n of xs is sorted
{-@ lma_isfn_set :: xs:_ -> x:_ -> n:{v:Nat |  v < size xs} -> m:{v:Nat | v <= n } 
      -> {(isSortedFstN (set xs n x) m) = (isSortedFstN xs m)} / [m] @-}

lma_isfn_set :: Ord a => Array a -> a -> Int -> Int -> Proof
lma_isfn_set xs x n 0 = ()
lma_isfn_set xs x n 1 = ()
lma_isfn_set xs x n m 
  = isSortedFstN (set xs n x) m
  -- === (((get (set xs n x) (m-2)) <= (get (set xs n x) (m-1))) && (isSortedFstN (set xs n x) (m-1)))
    ? (lma_gns xs n (m-2) x) &&& (lma_gns xs n (m-1) x)
  -- === (((get xs (m-2)) <= (get xs (m-1))) && (isSortedFstN (set xs n x) (m-1)))
    ? lma_isfn_set xs x n (m-1)
  -- === (((get xs (m-2)) <= (get xs (m-1))) && (isSortedFstN xs (m-1)))
  === isSortedFstN xs m
  *** QED


-- lemma showing (isSortedFstN xs n) => (isSortedFstN xs m) for all m < n
{-@ lma_isfn1 :: xs:_ -> n:{v:Nat | v <= size xs && (isSortedFstN xs v)} -> m:{v:Nat | v <= n} 
      -> {isSortedFstN xs m} / [n-m] @-}
lma_isfn1 :: Ord a => Array a -> Int -> Int -> Proof
lma_isfn1 xs n 0 = () -- TODO: this line is necessary?
lma_isfn1 xs n m | m == (n) = ()
           | otherwise = True
    ? lma_isfn1 xs n (m+1)
  -- === isSortedFstN xs (m+1)
  -- === (((get xs (m-1)) <= (get xs (m))) && (isSortedFstN xs (m)))
  === (isSortedFstN xs (m))
  *** QED

{- TODO: CANNOT prove going the other direction 
lma_isfn1 xs n m | m == (n-1) = ()
           | otherwise = (isSortedFstN xs (m))
  === (((get xs (m-1)) <= (get xs (m))) && (isSortedFstN xs (m)))
  === isSortedFstN xs (m+1)
    ? lma_isfn1 xs n (m+1)
  === True
  *** QED
-}