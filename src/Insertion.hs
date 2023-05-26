{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}
-- {-@ LIQUID "--checks=lma_insert_eq" @-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}

module Insertion where

import           Prelude
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import qualified Language.Haskell.Liquid.Bag as B
import           ProofCombinators
import           Array
import           Order
import           Equivalence

import qualified Unsafe.Linear as Unsafe

#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
#else
import           Array.List as A
#endif

import qualified Array as A


--------------------------------------------------------------------------------
-- | Implementations
--------------------------------------------------------------------------------


{-@ reflect insert @-}
{-@ insert :: xs:_ -> x:_ -> n:{v:Nat | v < A.size xs}
       -> ys:{A.size ys == A.size xs} / [n] @-}

insert :: HasPrimOrd a => A.Array a -> a -> Int -> A.Array a
insert !xs !x 0 = A.set xs 0 x  -- first element is sorted
insert !xs !x !n =              -- sort the nth element into the first n+1 elements
  let (!a, !xs') = A.get2 xs (n-1)
  in if x < a
     then let !xs'' = A.set xs' (n) a
          in insert xs'' x (n - 1)
     else A.set xs' n x

{-
// JL: inplace c style of the above insert method.
void insert(int* xs, int x, int n){
  if(n == 0) {
    xs[0] = x;
    return;
  }
  int a = xs[n-1];
  if(x < a){
    // swapping
    xs[n] = a;
    insert(xs,x,n-1); // tail recursive
  }else{
    xs[n] = x;
  }
}
-}


{-@ reflect isort @-}
{-@ isort :: xs:_ -> n:{v:Nat | v <= A.size xs}
      -> ys:{A.size ys == A.size xs} / [n] @-}
-- | Sort in-place.
isort :: HasPrimOrd a => A.Array a -> Int -> A.Array a
isort xs n
  | ( s == 0 ) = xs'
  | ( s == 1 ) = xs'
  | ( n == 0 ) = xs'
  | otherwise  = let !(a, xs'') = (A.get2 xs' (s-n))
                 in isort (insert xs'' a (s-n)) (n-1) -- switch to tail recursive
    where
      (s, xs') = A.size2 xs

{-
// JL: inplace c style of the above isort method.
void isort(int* xs, int n, int s){
  if(s == 0 || s == 1 || n == 0){
    return;
  }
  int a = xs[s-n];
  insert(xs, a, (s-n));
  isort(xs, n-1, s); // tail recursive
}

int main(void){
  // top
  isort(arr, sz, sz);
}
-}

{-@ isort_top :: xs:_ -> ys:{isSorted ys && (toBag xs == toBag ys)} @-}
-- | Sort a copy of the input array.
isort_top :: HasPrimOrd a => A.Array a -> A.Array a
isort_top xs0 =
    if s <= 1 then xs0 else
      let Ur cpy = A.alloc s hd (Unsafe.toLinear (\tmp -> Ur (A.copy xs2 0 tmp 0 s)))
          ys = isort cpy s
      in ys
        ? ((lma_isort xs2 s) &&& (lma_isort_eq xs2 s)
        &&& (lma_toBag_toBagLeft xs2 (size xs2)) &&& (lma_toBag_toBagLeft ys (size ys)))
  where
    (s, xs1) = A.size2 xs0
    (hd, xs2) = A.get2 xs1 0

--------------------------------------------------------------------------------
-- | Proofs for Sortedness
--------------------------------------------------------------------------------

{-@ lma_insert_fix :: xs:_ -> x:_ -> n:{v:Nat | v < A.size xs} -> m:{v:Nat | v > n && v < A.size xs}
      -> {A.get (insert xs x n) m == A.get xs m} / [n] @-}
lma_insert_fix :: HasPrimOrd a => A.Array a -> a -> Int -> Int -> Proof
lma_insert_fix xs x 0 m
  = A.get (insert xs x 0) m
  -- === A.get (A.set xs 0 x) m
    ? (lma_gns xs 0 m x)
  === A.get xs m
  *** QED

lma_insert_fix xs x n m
  | x < (A.get xs (n-1))
    = A.get (insert xs x n) m
    -- === A.get (insert (A.set xs (n) (A.get xs (n-1))) x (n - 1)) m
      ? (lma_insert_fix (A.set xs (n) (A.get xs (n-1))) x (n-1) m)
    -- === A.get (A.set xs (n) (A.get xs (n-1))) m
      ? (lma_gns xs n m (A.get xs (n-1)))
    === A.get xs m
    *** QED
  | otherwise
    = A.get (insert xs x n) m
    -- === A.get (A.set xs n x) m
      ? (lma_gns xs n m x)
    === A.get xs m
    *** QED


{-@ lma_insert_max :: xs:_ -> x:_ -> y:_ -> n:{Nat | (n < A.size xs) && (n > 0) && (x <= y) && ((A.get xs (n-1)) <= y)}
      -> {y >= A.get (insert xs x n) n} / [n] @-}
lma_insert_max :: HasPrimOrd a => A.Array a -> a -> a -> Int -> Proof
lma_insert_max xs x y n
  | x < (A.get xs (n-1))
    = y
    =>= A.get xs (n-1)
      ? (lma_gs xs n (A.get xs (n-1)))
    -- === A.get (A.set xs (n) (A.get xs (n-1))) n
      ? (lma_insert_fix (A.set xs (n) (A.get xs (n-1))) x (n-1) n)
    -- === A.get (insert (A.set xs (n) (A.get xs (n-1))) x (n-1)) n
    === A.get (insert xs x n) n
    *** QED
  | otherwise
    = y
    =>= x
      ? (lma_gs xs n x)
    -- === A.get (A.set xs n x) n
    === A.get (insert xs x n) n
    *** QED

{-@ lma_insert :: xs:_ -> x:_ -> n:{ Nat | n < A.size xs && (isSortedFstN xs n)}
      -> ys:{isSortedFstN (insert xs x n) (n+1)} / [n] @-}
lma_insert :: HasPrimOrd a => A.Array a -> a -> Int -> Proof
lma_insert _ _ 0 = ()
lma_insert xs x n
  | x < (A.get xs (n-1)) && (n >= 2)
    = let
        xs' = (A.set xs (n) (A.get xs (n-1)))
        -- ys  = (insert xs' x (n-1))
      in isSortedFstN (insert xs x n) (n+1)
        -- === isSortedFstN ys (n+1)
        -- === (((A.get ys (n-1)) <= (A.get ys n)) && (isSortedFstN ys n))
          ? (lma_insert xs' x (n-1 ? (lma_isfn_set xs (A.get xs (n-1)) n (n-1))))
        -- === (A.get ys (n-1)) <= (A.get ys (n))
          ? (lma_insert_fix xs' x (n-1) n)
        -- === (A.get ys (n-1)) <= (A.get xs' (n))
          ? (lma_gs xs n (A.get xs (n-1)))
        -- === (A.get ys (n-1)) <= (A.get xs (n-1))
          ? (lma_insert_max xs' x (A.get xs (n-1)) (n-1 ? (lma_gns xs n (n-2) (A.get xs (n-1)))))
        === True
        *** QED
  | x < (A.get xs (n-1)) && (n < 2)
    = let
        xs' = (A.set xs (n) (A.get xs (n-1)))
        -- ys  = (insert xs' x (n-1))
      in isSortedFstN (insert xs x n) (n+1)
        -- === isSortedFstN ys (n+1)
        -- === (((A.get ys (n-1)) <= (A.get ys n)) && (isSortedFstN ys n))
          ? (lma_insert xs' x (n-1 ? (lma_isfn_set xs (A.get xs (n-1)) n (n-1))))
        -- === (A.get ys (n-1)) <= (A.get ys (n))
          ? (lma_insert_fix xs' x (n-1) n)
        -- === (A.get ys (n-1)) <= (A.get xs' (n))
          ? (lma_gs xs n (A.get xs (n-1)))
        -- === (A.get ys (n-1)) <= (A.get xs (n-1))
          ? (lma_gs xs' 0 x)-- A.get ys (n-1) === get (insert xs' x (n-1)) (n-1) ===
        -- === x <= (A.get xs (n-1))
        === True
        *** QED
  | otherwise
    = let
        -- xs' = (A.set xs n x)
        -- ys  = (insert xs' x (n-1))
      in isSortedFstN (insert xs x n) (n+1)
        -- === isSortedFstN xs' (n+1)
        -- === (((A.get xs' (n-1)) <= (A.get xs' n)) && (isSortedFstN xs' n))
          ? (lma_isfn_set xs x n n)
        -- === (((A.get xs' (n-1)) <= (A.get xs' n)) && (isSortedFstN xs n))
        -- === ((A.get xs' (n-1)) <= (A.get xs' n))
          ? ((lma_gns xs n (n-1) x) &&& (lma_gs xs n x))
        -- === ((A.get xs (n-1)) <= x)
        === True
        *** QED


{-@ lma_isort :: xs:_ -> n:{ Nat | n > 0 && n <= A.size xs && isSortedFstN xs (A.size xs - n)}
      -> {isSortedFstN (isort xs n) (A.size xs)} / [n] @-}
lma_isort :: HasPrimOrd a => A.Array a -> Int -> Proof
lma_isort xs n
  | (A.size xs == 0) = ()
  | (A.size xs == 1) = ()
  | (n == 1)
    = let
        s = A.size xs
        x  = (A.get xs (s-1))
        zs = (insert xs x (s-1))
      in True
        -- === isSortedFstN xs (s-1)
          ? (lma_insert xs x (s-1))
        === isSortedFstN zs s
        -- === isSortedFstN (isort zs 0) s
        === isSortedFstN (isort xs 1) s
        *** QED
  | otherwise
    = let
        s = A.size xs
        x  = (A.get xs (s-n))
        zs = (insert xs x (s-n))
      in True
        -- === isSortedFstN xs (s - n)
          ? (lma_insert xs x (s-n))
        -- === isSortedFstN (insert xs x (s-n)) (s - (n - 1))
        -- === isSortedFstN zs (s - (n - 1))
          ? (lma_isort zs (n-1))
        -- === isSortedFstN (isort zs (n-1)) (s-n+2)
        -- === isSortedFstN (isort zs (n-1)) (s-(n-1))
        *** QED

--------------------------------------------------------------------------------
-- | Proofs for Equivalence
--------------------------------------------------------------------------------

{-@ lma_insert_eq :: xs:_ -> x:_ -> n:{v:Nat | v < A.size xs}
       -> ys:{(toBagLeft (insert xs x n) (n+1)) == (B.put x (toBagLeft xs n))} / [n] @-}
lma_insert_eq :: HasPrimOrd a => A.Array a -> a -> Int -> Proof
lma_insert_eq xs x 0
  = toBagLeft (insert xs x 0) 1
  -- === toBagLeft (A.set xs 0 x) 1
  -- === B.put (A.get (A.set xs 0 x) 0) (toBagLeft xs 0)
    ? (lma_gs xs 0 x)
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
        ? (lma_gs xs n (A.get xs (n-1)))
      -- === B.put x (B.put (A.get xs (n-1)) (toBagLeft xs (n-1)))
      === B.put x (toBagLeft xs n)
      *** QED
  | otherwise
    = toBagLeft (insert xs x n) (n+1)
    -- === toBagLeft (A.set xs n x) (n+1)
    -- === B.put (A.get (A.set xs n x) n) (toBagLeft (A.set xs n x) n)
      ? ((lma_gs xs n x) &&& (lma_set_equal xs x n n))
    === (B.put x (toBagLeft xs n))
    *** QED


{-@ lma_insert_eq_all :: xs:_ -> n:{ Nat | n < A.size xs} -> m:{ Nat | n + 1 <= m && m <= A.size xs}
       -> {(toBagLeft (insert xs (A.get xs n) n) m) == (toBagLeft xs m)} / [m] @-}
lma_insert_eq_all :: HasPrimOrd a => A.Array a -> Int -> Int -> Proof
lma_insert_eq_all xs n m
  | m == n + 1  = toBagLeft (insert xs x n) m
                  ? (lma_insert_eq xs x n)
                -- === B.put x (toBagLeft xs n)
                -- === toBagLeft xs m
                *** QED
  | otherwise   = let
                    y = A.get (insert xs x n) (m-1) ? (lma_insert_fix xs x n (m-1))
                  in toBagLeft (insert xs x n) m
                  -- === B.put y (toBagLeft (insert xs x n) (m-1))
                    ? (lma_insert_eq_all xs n (m-1))
                  === B.put y (toBagLeft xs (m-1))
                  -- === toBagLeft xs m
                  *** QED
    where
      x = A.get xs n


{-@ lma_isort_eq :: xs:_ -> n:{ Nat | n <= A.size xs }
       -> { toBagEqual (isort xs n) xs } @-}
lma_isort_eq :: HasPrimOrd a => A.Array a -> Int -> Proof
lma_isort_eq xs n
  | (A.size xs == 0) = ()
  | (A.size xs == 1) = ()
  | (n == 0)         = ()
  | otherwise        =
    let
      s = A.size xs
      x  = (A.get xs (s-n))
      zs = (insert xs x (s-n))
    in toBagLeft (isort xs n) s
      -- === toBagLeft (isort zs (n-1)) s
        ? (lma_isort_eq zs (n-1))
      -- === toBagLeft zs s
        ? (lma_insert_eq_all xs (s-n) s)
      -- === toBagLeft xs s
      *** QED
