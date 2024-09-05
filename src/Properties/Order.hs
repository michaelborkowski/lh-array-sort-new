{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}

{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-# LANGUAGE GADTs #-}

module Properties.Order where

import           Prelude hiding ((++))
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import           Array

#ifdef MUTABLE_ARRAYS
import           Array.Mutable
#else
import           Array.List
#endif

import qualified Data.Primitive.Types as P

--------------------------------------------------------------------------------

{-@ reflect isSorted @-}
isSorted :: HasPrimOrd a => Array a -> Bool
isSorted xs = isSortedFstN xs (size xs)

{-@ reflect isSortedFstN @-}
{-@ isSortedFstN :: xs:_ -> m:{n:Nat | n <= size xs} -> b:_ / [m] @-}
isSortedFstN :: HasPrimOrd a => Array a -> Int -> Bool
isSortedFstN xs 0 = True
isSortedFstN xs 1 = True
isSortedFstN xs n = ((get xs (n-2)) <= (get xs (n-1))) && (isSortedFstN xs (n-1))

{-@ reflect isSorted' @-}
isSorted' :: HasPrimOrd a => Array a -> Bool
isSorted' xs = isSortedBtw xs 0 (size xs)

{-@ reflect isSortedBtw @-}
{-@ isSortedBtw :: xs:(Array a) -> { i:Int | i >= 0 }
                                -> { j:Int | i <= j && j <= size xs } -> Bool / [j-i] @-}
isSortedBtw :: HasPrimOrd a => Array a -> Int -> Int -> Bool
isSortedBtw xs i j | i + 1 >= j  = True
                   | otherwise   = (get xs i <= get xs (i+1)) && isSortedBtw xs (i+1) j

{-@ lem_isSortedBtw_right :: xs:(Array a) -> {i:Int | 0 <= i } -> { j:Int | i < j-1 && j <= size xs }
        -> { pf:_ | isSortedBtw xs i j <=> ((get xs (j-2) <= get xs (j-1)) && isSortedBtw xs i (j-1)) } / [j-i] @-}
lem_isSortedBtw_right :: Ord a => Array a -> Int -> Int -> Proof
lem_isSortedBtw_right xs i j | i + 2 == j  = ()
                             | otherwise   = () ? lem_isSortedBtw_right xs (i+1) j

{-@ lem_isSortedBtw_build_right :: xs:(Array a) -> {i:Int | 0 <= i }
                                -> { j:Int | i <= j && j <= size xs && isSortedBtw xs i j &&
                                             ( i == j || get xs (j-1) <= get xs j ) }
                                -> { pf:_ | isSortedBtw xs i (j+1) } / [j-i] @-}
lem_isSortedBtw_build_right :: Ord a => Array a -> Int -> Int -> Proof
lem_isSortedBtw_build_right xs i j | i     == j  = ()
                                   | i + 1 == j  = ()
                                   | otherwise   = () ? lem_isSortedBtw_build_right xs (i+1) j

{-@ lem_isSortedBtw_set_right :: xs:(Array a) -> {i:Int | 0 <= i }
                                -> { j:Int | i <= j && j < size xs && isSortedBtw xs i j }
                                -> { v:a   | ( i == j || get xs (j-1) <= v ) }
                                -> { pf:_  | isSortedBtw (set xs j v) i (j+1) } / [j-i] @-}
lem_isSortedBtw_set_right :: HasPrimOrd a => Array a -> Int -> Int -> a -> Proof
lem_isSortedBtw_set_right xs i j v
    | i     == j  = ()
    | i + 1 == j  = () ? lma_gns xs j i     v
                       ? lma_gs  xs (i+1)   v
    | otherwise   = () ? lem_isSortedBtw_set_right xs (i+1) j v
                      -- IH gives us: isSortedBtw (set xs j v) (i+1) v where i < j-1
                       ? lma_gns xs j i     v
                       ? lma_gns xs j (i+1) v

{-@ lem_isSortedBtw_narrow :: xs:(Array a) -> { i:Int | 0 <= i }
                                           -> { i':Int | i <= i' } -> { j':Int | i' <= j' }
                                           -> { j:Int | j' <= j && j <= size xs && isSortedBtw xs i j }
                                           -> { pf:_  | isSortedBtw xs i' j' } / [ i' - i + j - j'] @-}
lem_isSortedBtw_narrow :: Ord a => Array a -> Int -> Int -> Int -> Int -> Proof
lem_isSortedBtw_narrow xs i i' j' j
    | i+1 < j && i < i'      = () ? lem_isSortedBtw_narrow xs (i+1) i' j' j
    | i+1 < j && j' < j      = () ? lem_isSortedBtw_narrow xs i i' j' (j-1
                                  ? lem_isSortedBtw_right  xs i j )
    | otherwise              = ()

{-@ lem_isSortedBtw_compose :: xs:(Array a) -> { i:Int | 0 <= i } -> { j:Int | i <= j }
                                            -> { k:Int | j < k && k <= size xs &&
                                                         isSortedBtw xs i j && isSortedBtw xs j k &&
                                                       ( i == j || get xs (j-1) <= get xs j ) }
                                            -> { pf:_ | isSortedBtw xs i k } / [j - i] @-}
lem_isSortedBtw_compose :: HasPrimOrd a => Array a -> Int -> Int -> Int -> Proof
lem_isSortedBtw_compose xs i j k | i == j      = ()
                                 | i + 1 == j  = ()
                                 | otherwise   = () ? lem_isSortedBtw_right   xs i j
                                                    ? lem_isSortedBtw_compose xs i (j-1) k

{-@ lem_isSorted_append :: { xs:Array a | isSorted' xs }
        -> { ys:Array a | isSorted' ys && 
                          token xs == token ys && right xs == left ys &&
                          ( size xs == 0 || size ys == 0 || get xs ((size xs)-1) <= get ys 0) }
        -> { pf:_ | isSorted' (append xs ys) } @-}
lem_isSorted_append :: HasPrimOrd a => Array a -> Array a -> Proof
lem_isSorted_append xs ys 
  = if size ys == 0 
    then lem_slice_append xs ys
        ? lem_isSortedBtw_from_slice (append xs ys) 0         (size xs) 
    else lem_isSortedBtw_compose (append xs ys) 0 (size xs) (size xs + size ys
        ? lem_slice_append xs ys
        ? lem_isSortedBtw_from_slice (append xs ys) 0         (size xs) 
        ? lem_isSortedBtw_from_slice (append xs ys) (size xs) (size xs + size ys)
        ? (if size ys > 0 then lem_get_append_right xs ys (size xs) else ())
        ? (if size xs > 0 then lem_get_append_left  xs ys (size xs - 1) else ()) )

{-@ lem_isSortedBtw_from_left_append :: xs:_ 
        -> { ys:_ | token xs == token ys && right xs == left ys }
        -> i:Nat -> { j:Nat | i <= j && j <= size xs && isSortedBtw xs i j }
        -> { pf:_ | isSortedBtw (append xs ys) i j } / [j - i] @-}
lem_isSortedBtw_from_left_append :: HasPrimOrd a => Array a -> Array a -> Int -> Int -> Proof
lem_isSortedBtw_from_left_append xs ys i j
    | i+1 >= j  = ()
    | otherwise = lem_isSortedBtw_from_left_append xs ys (i+1) j 
                ? lem_get_append_left xs ys i
                ? lem_get_append_left xs ys (i+1)

{-@ lem_isSortedBtw_from_right_append :: xs:_ 
        -> { ys:_ | token xs == token ys && right xs == left ys }
        -> { i:Nat | size xs <= i }
        -> { j:Nat | i <= j && j <= size xs + size ys && 
                     isSortedBtw ys (i-size xs) (j-size xs) }
        -> { pf:_ | isSortedBtw (append xs ys) i j } / [j - i] @-}
lem_isSortedBtw_from_right_append :: HasPrimOrd a => Array a -> Array a -> Int -> Int -> Proof
lem_isSortedBtw_from_right_append xs ys i j
    | i+1 >= j  = ()
    | otherwise = lem_isSortedBtw_from_right_append xs ys (i+1) j 
                ? lem_get_append_right xs ys i           
                ? lem_get_append_right xs ys (i+1)           

{-@ lem_isSorted_copy :: { xs:_ | isSorted' xs } -> { xi:Nat | xi <= size xs } -> ys:_
        -> { yi:Nat | yi <= size ys && isSortedBtw ys 0 yi }
        -> { n:Nat  | xi + n <= size xs && yi + n <= size ys &&
                      ( xi == size xs || yi == 0 || get xs xi >= get ys (yi-1) ) }
        -> { zs:_   | isSortedBtw (copy xs xi ys yi n) 0 (yi+n)} / [n] @-}
lem_isSorted_copy :: HasPrimOrd a => Array a -> Int -> Array a -> Int -> Int -> Proof
lem_isSorted_copy xs xi ys yi 0 = ()
lem_isSorted_copy xs xi ys yi 1
    = () ? lem_isSorted_copy xs xi ys yi 0
        -- IH gives us:  isSortedBtw (copy xs xi ys yi 0) 0 yi
        -- To get:       isSortedBtw (copy xs xi ys yi 1) 0 (yi+1)
         ? lem_isSortedBtw_set_right (copy xs xi ys yi 0) 0 (yi) (get xs xi)
lem_isSorted_copy xs xi ys yi n
    = () ? lem_isSorted_copy xs xi ys yi (n-1)
         ? lem_isSortedBtw_set_right (copy xs xi ys yi (n-1)) 0 (yi+n-1) (get xs (xi+n-1)
             ? lma_gs                (copy xs xi ys yi (n-2))   (yi+n-2) (get xs (xi+n-2))
             ? lem_isSortedBtw_narrow xs 0 (xi+n-2) (xi+n) (size xs) )

{-@ lem_isSortedBtw_slice' :: { xs:(Array a) | isSorted' xs} -> { i:Int | 0 <= i }
                                    -> { j:Int | i <= j && j <= size xs }
                                    -> { i':Int | 0 <= i' } -> { j':Int | i' <= j' && j' <= j-i }
                                    -> { pf:_  | isSortedBtw (slice xs i j) i' j' } / [ j'- i' ] @-}
lem_isSortedBtw_slice' :: Ord a => Array a -> Int -> Int -> Int -> Int -> Proof
lem_isSortedBtw_slice' xs i j i' j'
    | i' + 1 >= j'  = ()
    | otherwise     = () ? lem_isSortedBtw_slice' xs i j (i'+1) j'
                         ? lem_get_slice xs i j (i+i')
                         ? lem_get_slice xs i j (i+i'+1)
                         ? lem_isSortedBtw_narrow xs 0 (i+i') (i+j') (size xs)

{-@ lem_isSortedBtw_slice :: { xs:(Array a) | isSorted' xs} -> { i:Int | 0 <= i }
                                    -> { j:Int | i <= j && j <= size xs}
                                    -> { pf:_  | isSorted' (slice xs i j) } @-}
lem_isSortedBtw_slice :: Ord a => Array a -> Int -> Int -> Proof
lem_isSortedBtw_slice xs i j = lem_isSortedBtw_slice' xs i j 0 (j-i)

{-@ lem_isSortedBtw_from_slice' :: xs:(Array a) -> { i:Int | 0 <= i }
                                    -> { j:Int | i <= j && j <= size xs && isSorted' (slice xs i j) }
                                    -> { i':Int | i <= i' } -> { j':Int | i' <= j' && j' <= j }
                                    -> { pf:_  | isSortedBtw xs i' j' } / [ j'- i' ] @-}
lem_isSortedBtw_from_slice' :: Ord a => Array a -> Int -> Int -> Int -> Int -> Proof
lem_isSortedBtw_from_slice' xs i j i' j'
    | i' + 1 >= j'  = ()
    | otherwise     = () ? lem_isSortedBtw_from_slice' xs i j (i'+1) j'
                         ? lem_get_slice xs i j i'
                         ? lem_get_slice xs i j (i'+1)
                         ? lem_isSortedBtw_narrow (slice xs i j) 0 (i'-i) (j'-i) (j-i)

{-@ lem_isSortedBtw_from_slice :: xs:(Array a)  -> { i:Int | 0 <= i }
                                    -> { j:Int | i <= j && j <= size xs && isSorted' (slice xs i j)}
                                    -> { pf:_  |  isSortedBtw xs i j } @-}
lem_isSortedBtw_from_slice :: HasPrimOrd a => Array a -> Int -> Int -> Proof
lem_isSortedBtw_from_slice xs i j = lem_isSortedBtw_from_slice' xs i j i j
 

-- lemma showing set preserves sortedness of indices before n, and if the new
-- element is greater than the previous, xs is sorted up to n+1
{-@ lma_set_ps :: xs:_ -> n:{m:Nat | m < size xs && m > 0 } -> x:{(isSortedFstN xs n) && ((x >= (get xs (n-1))))}
      -> { pf:_ | isSortedFstN (set xs n x) (n+1)} / [n]@-}
lma_set_ps :: HasPrimOrd a => Array a -> Int -> a -> Proof
lma_set_ps xs 1 x
  = isSortedFstN (set xs 1 x) 2
  -- === (((get (set xs 1 x) 0) <= (get (set xs 1 x) 1)) && (isSortedFstN (set xs 1 x) 1))
    ? ((lma_gns xs 1 0 x) &&& (lma_gs xs 1 x))
  -- === (((get xs 0) <= x) && (isSortedFstN (set xs 1 x) 1))
  -- === isSortedFstN (set xs 1 x) 1
  === True
  *** QED
lma_set_ps xs n x
  = isSortedFstN (set xs n x) (n+1)
  -- === (((get (set xs n x) (n-1)) <= (get (set xs n x) (n))) && (isSortedFstN (set xs n x) (n)))
    ? ((lma_gns xs n (n-1) x) &&& (lma_gs xs n x))
  -- === (((get xs (n-1)) <= x) && (isSortedFstN (set xs n x) (n)))
  -- === (isSortedFstN (set xs n x) (n))
  -- === (((get (set xs n x) (n-2)) <= (get (set xs n x) (n-1))) && (isSortedFstN (set xs n x) (n-1)))
    ? ((lma_gns xs n (n-2) x) &&& (lma_gns xs n (n-1) x))
  -- === (((get xs (n-2)) <= (get xs (n-1))) && (isSortedFstN (set xs n x) (n-1)))
  -- === isSortedFstN (set xs n x) (n-1)
    ? lma_isfn_set xs x n (n-1)
  -- === isSortedFstN xs (n-1)
  === True
  *** QED

-- lemma showing that isSorted xs implies xs[n] <= xs[n+m]
{-@ lma_is_le :: xs:{isSorted xs} -> n:{v:Nat | v < size xs}
      -> {(0 < n) => (get xs (n-1) <= get xs n)} / [n] @-}
lma_is_le :: HasPrimOrd a => Array a -> Int -> Proof
lma_is_le xs n = () ? (lma_is_isfn xs (n+1))
  -- = get xs (n-1) <= get xs n
  --   ? (lma_is_isfn xs (n+1))
  -- === True
  -- *** QED

-- lemma showing that isSorted xs implies isSorted for first n when n in range
{-@ lma_is_isfn :: xs:{isSorted xs} -> n:{v:Nat |  v <= size xs}
      -> {pf:_ | isSortedFstN xs n} / [n] @-}
lma_is_isfn :: HasPrimOrd a => Array a -> Int -> Proof
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
lma_isfn_set :: HasPrimOrd a => Array a -> a -> Int -> Int -> Proof
lma_isfn_set xs x n 0 = ()
lma_isfn_set xs x n 1 = ()
lma_isfn_set xs x n m
  = isSortedFstN (set xs n x) m
  -- === (((get (set xs n x) (m-2)) <= (get (set xs n x) (m-1))) && (isSortedFstN (set xs n x) (m-1)))
    ? ((lma_gns xs n (m-2) x) &&& (lma_gns xs n (m-1) x))
  -- === (((get xs (m-2)) <= (get xs (m-1))) && (isSortedFstN (set xs n x) (m-1)))
    ? lma_isfn_set xs x n (m-1)
  -- === (((get xs (m-2)) <= (get xs (m-1))) && (isSortedFstN xs (m-1)))
  === isSortedFstN xs m
  *** QED

-- lemma showing (isSortedFstN xs n) => (isSortedFstN xs m) for all m < n
{-@ lma_isfn1 :: xs:_ -> n:{v:Nat | v <= size xs && (isSortedFstN xs v)} -> m:{v:Nat | v <= n}
      -> {pf:_ | isSortedFstN xs m} / [n-m] @-}
lma_isfn1 :: HasPrimOrd a => Array a -> Int -> Int -> Proof
lma_isfn1 xs n 0 = () -- TODO: this line is necessary?
lma_isfn1 xs n m | m == (n) = ()
           | otherwise = True
    ? lma_isfn1 xs n (m+1)
  -- === isSortedFstN xs (m+1)
  -- === (((get xs (m-1)) <= (get xs (m))) && (isSortedFstN xs (m)))
  === (isSortedFstN xs (m))
  *** QED
