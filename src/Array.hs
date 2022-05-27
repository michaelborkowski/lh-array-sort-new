{-# LANGUAGE CPP #-}

{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Array
{-  (
    -- * Array type
    Array

    -- * Construction and querying
  , make, get, set, slice, size, append, swap

    -- * Linear versions
  , size2, get2

    -- * Convert to/from lists
  , fromList, toList

    -- * LiqidHaskell lemmas
  , lma_gs, lma_gns, lma_swap, lma_swap_eql
  ) -} where

import           Array.List (lma_gs_list, lma_gns_list)

#ifdef MUTABLE_ARRAYS
import           Array.Mutable
#else
import           Array.List
#endif

import           Language.Haskell.Liquid.ProofCombinators

--------------------------------------------------------------------------------

{-@ reflect splitMid @-}
{-@ splitMid :: xs:(Array a)
      -> {t:_ | token (fst t) == token xs && token (snd t) == token xs &&
                right (fst t) == left (snd t) &&
                right (fst t) == left xs + div (size xs) 2 &&
                left (fst t) == left xs && right (snd t) == right xs &&
                size (fst t) == div (size xs) 2 &&
                size (snd t) == size xs - div (size xs) 2 &&
                size xs = (size (fst t)) + (size (snd t)) } @-}
splitMid :: Ord a => Array a -> (Array a, Array a)
splitMid xs = (slice xs 0 m, slice xs m n)   
  where
    n = size xs
    m = n `div` 2

--------------------------------------------------------------------------------
-- | Proofs
--------------------------------------------------------------------------------

{-@ lma_gs :: xs:_ -> n:{v:Nat | v < size xs } -> x:_
      -> {pf:_ | get (set xs n x) n = x} @-}
lma_gs :: Array a -> Int -> a -> Proof
lma_gs arr n x = lma_gs_list (toList arr) n x

--{-@ lma_gs2 :: xs:_ -> n:{v:Nat | v < size xs } -> x:_
--      -> {pf:_ | fst (get2 (set xs n x) n) = x} @-}
--lma_gs2 :: Array a -> Int -> a -> Proof
--lma_gs2 xs n x = lma_gs xs n x

{-@ lma_gns :: xs:_ -> n:{v:Nat | v < size xs }
          -> m:{v:Nat | v /= n && v < size xs } -> x:_
          -> { pf:_ | get (set xs n x) m = get xs m} @-}
lma_gns :: Array a -> Int -> Int -> a -> Proof
lma_gns arr n m x = lma_gns_list (toList arr) n m x

--{-@ lma_gns2 :: xs:_ -> n:{v:Nat | v < size xs } 
--          -> m:{v:Nat | v /= n && v < size xs } -> x:_
--          -> { pf:_ | fst (get2 (set xs n x) m) == fst (get2 xs m) } @-}
--lma_gns2 :: Array a -> Int -> Int -> a -> Proof
--lma_gns2 xs n m x = lma_gns xs n m x

-- advanced operations

{-@ reflect swap @-}
{-@ swap :: xs:(Array a) -> { i:Int | 0 <= i && i < size xs } 
                         -> { j:Int | 0 <= j && j < size xs }
                         -> { ys:(Array a) | size xs == size ys && token xs == token ys &&
                                             left xs == left ys && right xs == right ys } @-}
swap :: Array a -> Int -> Int -> Array a
swap xs i j = let xi  = get xs i
                  xs' = set xs i (get xs j)
               in set xs' j xi

{-@ lma_swap :: xs:(Array a) -> { i:Int | 0 <= i && i < size xs }
                             -> { j:Int | 0 <= j && j < size xs }
                             -> { pf:_  | get (swap xs i j) i == get xs j &&
                                          get (swap xs i j) j == get xs i } @-}
lma_swap :: Array a -> Int -> Int -> Proof
lma_swap xs i j
   | i == j     = () ? lma_gs  xs' j xi
   | i /= j     = () ? lma_gns xs' j i xi        --
                     ? lma_gs  xs  i (get xs j)  -- these two prove    get (swap xs i j) i == get xs j
                     ? lma_gs  xs' j xi          -- this proves        get (swap xs i j) j == get xs i
  where
    xi   = get xs  i
    xs'  = set xs  i (get xs j)

{-@ lma_swap_eql :: xs:(Array a) -> { i:Int | 0 <= i && i < size xs }
                                 -> { j:Int | 0 <= j && j < size xs }
                                 -> { k:Int | 0 <= k && k < size xs && k /= i && k /= j }
                                 -> { pf:_  | get (swap xs i j) k == get xs k } @-}
lma_swap_eql :: Array a -> Int -> Int -> Int -> Proof
lma_swap_eql xs i j k = () ? lma_gns xs' j k xi
                           ? lma_gns xs  i k (get xs j)
  where
    xi   = get xs  i
    xs'  = set xs  i (get xs j)
