{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--fuel=2"      @-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}

module Insertion where

import           Prelude hiding (max, min)
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

-- TODO List
-- [X] 1) Get insert to verify with just equivalence/token
-- [X] 2) Get isort to compile and verify with just equivalence/token
-- [ ] 3) Get insert to verify with sortedness too
-- [ ] 4) Get isort the code to fully verify
-- [ ] 5) Fully verify the top-level function
-- [ ] 6) Ask Chai about alloc stuff

{-@ reflect max @-}
{-@ max :: x:_ -> y:_ -> { z:_ | x <= z && y <= z } @-}
max :: Ord a => a -> a -> a
max x y = if x >= y then x else y

{-@ reflect min @-}
{-@ min :: x:_ -> y:_ -> { z:_ | z <= x && z <= y } @-}
min :: Ord a => a -> a -> a
min x y = if x <= y then x else y

--------------------------------------------------------------------------------
-- | Implementations
--------------------------------------------------------------------------------

{- @ lma_insert_fix :: xs:_ -> x:_ -> n:{v:Nat | v < A.size xs} -> m:{v:Nat | v > n && v < A.size xs}
      -> {A.get (insert xs x n) m == A.get xs m} / [n] @-}
{- @ lma_insert_max :: xs:_ -> x:_ -> y:_ 
      -> n:{Nat | (n < A.size xs) && (n > 0) && (x <= y) && ((A.get xs (n-1)) <= y)}
      -> {y >= A.get (insert xs x n) n} / [n] @-}

{-@ reflect insert_func @-}
{-@ insert_func :: xs:_ -> x:_ 
           -> { i:Nat | i < A.size xs }
           -> { ys:_  | A.size ys == A.size xs && token xs == token ys } / [i] @-} 
insert_func :: Ord a => A.Array a -> a -> Int -> A.Array a                      
insert_func xs x 0 = A.set xs 0 x        
insert_func xs x i = 
    if x < a then insert_func (A.set xs i a) x (i - 1)
             else A.set xs i x           
  where 
    a = A.get xs (i-1)

{-@ lem_insert_func_preserved ::     

{-@ lem_insert_func_boundary :: xs:_ -> x:_ 
           -> { i:Nat | 0 < i && i < A.size xs }
           -> { pf:_  | A.get (insert_func xs x i) i == max x (A.get xs (i-1)) } / [i] @-} 
lem_insert_func_boundary :: Ord a => A.Array a -> a -> Int -> Proof
lem_insert_func_boundary xs x i 
    | x < a     =   lem_insert_func_sorted_beyond xs' x (i-1)
                  ? lma_gs xs i a
    | otherwise =   lma_gs xs i x
  where 
    a    = A.get xs (i-1)
    xs'  = A.set xs i a    
          
{-@ lem_insert_func_sorted :: xs:_ -> x:_ 
           -> { i:Nat | i < A.size xs && isSortedBtw xs 0 i }
           -> { pf:_  | isSortedBtw (insert_func xs x i) 0 (i+1) } / [i] @-} 
lem_insert_func_sorted :: Ord a => A.Array a -> a -> Int -> Proof
lem_insert_func_sorted xs x 0 = () 
lem_insert_func_sorted xs x i 
    | x < a     =   lem_isSortedBtw_build_right (insert_func (A.set xs i a) x (i-1)) 
                      0 (i
 {-                       ? toProof ( A.get xs'' (i-1)
                              =<= max x (A.get xs' (i-2))
                                ? lma_gns xs i (i-2) a
                              =<= max x (A.get xs   (i-2)) ---
                                ? lem_isSortedBtw_narrow xs 0 (i-2) i i
                              =<= max x (A.get xs   (i-1))
                              =<= A.get xs    (i-1)
                                ? lma_gs          xs  i a
                              =<= A.get xs'  i            ---
                                ? lem_get_toSlice xs' xs'' i i (A.size xs) 
                              =<= A.get xs'' i            ---
                                )-}
                      )
                  ? lem_insert_func_sorted (A.set xs i a
                        ? lem_isSortedBtw_set_right xs 0 i a
                        ? lem_isSortedBtw_narrow (A.set xs i a) 0 0 (i-1) (i+1)
                      ) x (i-1)
    | otherwise =   lem_isSortedBtw_set_right xs 0 i x
 --                 ? lma_gs                    xs   i x
  where 
    a    = A.get xs (i-1)
    xs'  = A.set xs i a
    xs'' = insert_func (A.set xs i a) x (i-1)

{-
                       isSortedBtw ys 0 (i+1) &&
                       (i > 0  || A.get ys i <= x ) &&
                       (i == 0 || A.get ys i <= max x (A.get xs (i-1)) ) &&      
                                               toBag ys == toBag (A.set xs i x) && 
                       toSlice ys (i+1) (size xs) == toSlice xs (i+1) (size xs) &&      
-}
--
-- Given xs[0..i] sorted and xs[i] doesn't matter, insert x so that xs[0..i+1] is sorted.
{-@ insert :: xs:_ -> x:_        
           -> { i:Nat | i < A.size xs && isSortedBtw xs 0 i }
           -> { ys:_ | ys == insert_func xs x i &&          
                       A.size ys == A.size xs && token xs == token ys } / [i] @-} 
insert :: Ord a => A.Array a -> a -> Int -> A.Array a                             -- boundary cond ineq.
insert !xs !x 0 = A.set xs 0 x        ? lma_gs xs 0 x
                ? lem_toSlice_set_right xs 0 x 1 (A.size xs)
{-insert !xs !x 1 = 
  let (!a, !xs') = A.get2 xs 0 -- a is above xs[0..i-1], insert must preserve?
  in if x < a
     then A.set (A.set xs 0 x) 1 a    ? lma_gs (A.set xs 0 x) 1 a 
     else A.set xs        1 x         ? lma_gs xs 1 x-}
insert !xs !x !i =                 -- sort the element at offset i into the first i+1 elements
  let (!a, !xs') = A.get2 xs (i-1) -- a is above xs[0..i-1], insert must preserve?
  in if x < a
     then let !xs''  = A.set xs' i a        {- a <= max x a -}
                     ? lem_isSortedBtw_set_right xs 0 i a
                     ? lem_toSlice_set xs i a
              !xs''' = insert (xs'' ? lem_isSortedBtw_narrow xs'' 0 0 (i-1) (i+1)) x (i - 1)
           in xs''' -- ? lem_isSortedBtw_build_right xs''' 0 (i
 {-                       ? toProof ( A.get xs''' (i-1)
                              =<= max x (A.get xs'' (i-2))
                                ? lma_gns xs i (i-2) a
                              =<= max x (A.get xs   (i-2)) ---
                                ? lem_isSortedBtw_narrow xs 0 (i-2) i i
                              =<= max x (A.get xs   (i-1))
                              =<= A.get xs    (i-1)
                                ? lma_gs          xs  i a
                              =<= A.get xs''  i            ---
                                ? lem_get_toSlice xs'' xs''' i i (A.size xs) 
                              =<= A.get xs''' i            ---
                                ) -}
                      --  ? lma_gs          xs'  i a
                      --  ? lem_get_toSlice xs'' xs''' i i (A.size xs) 
                    --  )
                    -- ? lem_equal_slice_narrow xs'' xs''' i (i+1) (A.size xs) (A.size xs)
{-          ? toProof ( toBag (insert (set xs i a) x (i-1)) 
                   === toBag (set (set xs           i (get xs (i-1))) (i-1) x) -- by the IH
                     ? lma_gns xs i (i-1) x
                     ? lma_gs  xs i       x
                   === toBag (set (set xs           i (get (set xs i x) (i-1))) (i-1) (get (set xs i x) i))
                     ? lem_set_twice xs i (get (set xs i x) (i-1)) x
                   === toBag (set (set (set xs i x) i (get (set xs i x) (i-1))) (i-1) (get (set xs i x) i))
                   === toBag (swap (set xs i x) i (i-1))
                     ? lem_bag_swap (set xs i x) i (i-1)
                   === toBag (set xs i x) ) -}
     else A.set xs' i x                     {- x <= max x a -}
 --         ? lem_isSortedBtw_set_right xs 0 i x
          ? lem_toSlice_set_right     xs   i x (i+1) (A.size xs)
          ? lma_gs                    xs'  i x
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

{-

-- DO:-> { i:Nat | i < A.size xs && isSortedBtw xs 0 i }
--    -> { ys:_ | toBag xs == toBag ys && isSorted' ys &&
--                A.size xs == A.size ys && token xs == token ys } / [A.size xs - i] @- }
{-@ isort :: { xs:_ | A.size xs > 1 }  -> { i:Nat | i <= A.size xs }
      -> { ys:_ | toBag xs == toBag ys &&
                  A.size xs == A.size ys && token xs == token ys } / [A.size xs - i] @-}
isort :: Ord a => A.Array a -> Int -> A.Array a -- | Sort in-place.
isort xs n = xs
isort xs i = let (s, xs') = A.size2 xs {-in-}
               {-if s <= 1 then xs' 
               --else if i == 0 then xs'
               else let-} 
                 !(a, xs'') = (A.get2 xs' i) 
              in isort (insert xs'' a i) (i+1) 
               ? lem_bag_unchanged xs'' i

-}

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

{-
-- TODO: Postcondition: isSorted' ys &&
{-@ isort_top' :: { xs:_ | A.size xs > 1 } 
      -> { ys:_ | toBag xs == toBag ys && 
                  A.size xs == A.size ys && token xs == token ys } @-}
isort_top' :: Ord a => A.Array a -> A.Array a
isort_top' xs = isort xs 0

-- | Sort a copy of the input array.
-- TODO: Postcondition: isSorted' ys &&
{-@ isort_top :: { xs:_ | A.size xs > 1 } 
      -> { ys:_ | toBag xs == toBag ys && 
                  A.size xs == A.size ys && token xs == token ys } @-}
isort_top :: Ord a => A.Array a -> A.Array a
isort_top xs0 = let (n, xs1) = A.size2 xs0 in
    if n <= 1 then xs1 
    else let (hd, xs2) = A.get2 xs1 0
             Ur cpy = A.alloc s hd (Unsafe.toLinear (\tmp -> Ur (A.copy xs2 0 tmp 0 s)))
             ys = isort_top' cpy 0 --s
          in ys
        {-? ((lma_isort xs2 s) &&& (lma_isort_eq xs2 s)
        &&& (lma_toBag_toBagLeft xs2 (size xs2)) &&& (lma_toBag_toBagLeft ys (size ys)))-}
  where
    (s, xs1) = A.size2 xs0
-}

--{-@ isort_top :: xs:_ -> ys:{isSorted ys && (toBag xs == toBag ys)} @-}
---- | Sort a copy of the input array.
--isort_top :: Ord a => A.Array a -> A.Array a
--isort_top xs0 =
--    if s <= 1 then xs0 else
--      let Ur cpy = A.alloc s hd (Unsafe.toLinear (\tmp -> Ur (A.copy xs2 0 tmp 0 s)))
--          ys = isort cpy s
--      in ys
--        ? ((lma_isort xs2 s) &&& (lma_isort_eq xs2 s)
--        &&& (lma_toBag_toBagLeft xs2 (size xs2)) &&& (lma_toBag_toBagLeft ys (size ys)))
--  where
--    (s, xs1) = A.size2 xs0
--    (hd, xs2) = A.get2 xs1 0    
    
--------------------------------------------------------------------------------
-- | Proofs for Sortedness
--------------------------------------------------------------------------------

{-
{-@ lma_insert_fix :: xs:_ -> x:_ -> n:{v:Nat | v < A.size xs} -> m:{v:Nat | v > n && v < A.size xs}
      -> {A.get (insert xs x n) m == A.get xs m} / [n] @-}
lma_insert_fix :: Ord a => A.Array a -> a -> Int -> Int -> Proof
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

{-@ lma_insert_max :: xs:_ -> x:_ -> y:_ 
      -> n:{Nat | (n < A.size xs) && (n > 0) && (x <= y) && ((A.get xs (n-1)) <= y)}
      -> {y >= A.get (insert xs x n) n} / [n] @-}
lma_insert_max :: Ord a => A.Array a -> a -> a -> Int -> Proof
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
lma_insert :: Ord a => A.Array a -> a -> Int -> Proof
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
lma_isort :: Ord a => A.Array a -> Int -> Proof
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
-}