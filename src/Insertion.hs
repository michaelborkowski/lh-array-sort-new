
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}

module Insertion where

import           Prelude hiding (max)
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import qualified Language.Haskell.Liquid.Bag as B
import           ProofCombinators
import           Array
import           ArrayOperations
import Properties.Order
import Properties.Equivalence

import           Linear.Common
import qualified Unsafe.Linear as Unsafe

#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
#else
import           Array.List as A
#endif

import qualified Array as A

{-@ reflect max @-}
{-@ max :: x:_ -> y:_ -> { z:_ | x <= z && y <= z } @-}
max :: Ord a => a -> a -> a
max x y = if x >= y then x else y
 
--------------------------------------------------------------------------------
-- | Proofs for Sortedness and Equivalence
--------------------------------------------------------------------------------

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

{-@ lem_insert_func_untouched :: xs:_ -> x:_ 
           -> { i:Nat | i < A.size xs }
           -> { pf:_  | toSlice (insert_func xs x i) (i+1) (A.size xs) 
                                       == toSlice xs (i+1) (A.size xs) } / [i] @-} 
lem_insert_func_untouched :: Ord a => A.Array a -> a -> Int -> Proof
lem_insert_func_untouched xs x 0 
    = lem_toSlice_set_right xs 0 x 1 (A.size xs)
lem_insert_func_untouched xs x i 
    | x < a     =   lem_insert_func_untouched xs'   x (i-1)
                  ? lem_toSlice_set_right     xs  i a (i+1) (A.size xs)
    | otherwise =   lem_toSlice_set_right     xs  i x (i+1) (A.size xs)
  where 
    a    = A.get xs (i-1)
    xs'  = A.set xs i a      

{-@ lem_insert_func_boundary :: xs:_ -> x:_ 
           -> { i:Nat | 0 < i && i < A.size xs }
           -> { pf:_  | A.get (insert_func xs x i) i == max x (A.get xs (i-1)) } / [i] @-} 
lem_insert_func_boundary :: Ord a => A.Array a -> a -> Int -> Proof
lem_insert_func_boundary xs x i 
    | x < a     =   lem_insert_func_untouched xs' x (i-1)
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
lem_insert_func_sorted xs x 1 
    | x < a     =   lma_gs  (A.set xs 1 a) 0   x
                  ? lma_gns (A.set xs 1 a) 0 1 x 
                  ? lma_gs         xs      1   a
    | otherwise =   lma_gs         xs      1   x
                  ? lma_gns        xs      1 0 x
  where 
    a    = A.get xs 0  
lem_insert_func_sorted xs x i 
    | x < a     =   lem_isSortedBtw_build_right xs'' 0 (i
                        ? lem_insert_func_sorted (A.set xs i a
                              ? lem_isSortedBtw_set_right xs 0 i a
                              ? lem_isSortedBtw_narrow xs' 0 0 (i-1) (i+1)
                            ) x (i-1)
                        ? toProof ( A.get xs'' (i-1)
                                  ? lem_insert_func_boundary  xs' x (i-1)
                                === max x (A.get xs' (i-2))
                                  ? lma_gns xs i (i-2) a
                                === max x (A.get xs (i-2))
                            )
                        ? lem_isSortedBtw_narrow xs 0 (i-2) i i
                        ? toProof ( A.get xs'' i 
                                  ? lem_insert_func_untouched xs' x (i-1)
                                === A.get xs'  i
                                  ? lma_gs xs i a
                                === A.get xs   (i-1)
                            )
                      )
    | otherwise =   lem_isSortedBtw_set_right xs 0 i x
  where 
    a    = A.get xs (i-1)
    xs'  = A.set xs i a
    xs'' = insert_func (A.set xs i a) x (i-1)

{-@ lem_insert_func_equiv :: xs:_ -> x:_ 
           -> { i:Nat | i < A.size xs }
           -> { pf:_  | toBag (insert_func xs x i) == toBag (A.set xs i x) } / [i] @-} 
lem_insert_func_equiv :: Ord a => A.Array a -> a -> Int -> Proof
lem_insert_func_equiv xs x 0 = () 
lem_insert_func_equiv xs x i
    | x < a     = toProof ( toBag (insert (set xs i a) x (i-1))
                          ? lem_insert_func_equiv (set xs i a) x (i-1)
                        === toBag (set (set xs           i (get xs (i-1))) (i-1) x) -- by the IH
                          ? lma_gns xs i (i-1) x
                          ? lma_gs  xs i       x
                        === toBag (set (set xs           i (get (set xs i x) (i-1))) (i-1) (get (set xs i x) i))
                          ? lem_set_twice xs i (get (set xs i x) (i-1)) x
                        === toBag (set (set (set xs i x) i (get (set xs i x) (i-1))) (i-1) (get (set xs i x) i))
                        === toBag (swap (set xs i x) i (i-1))
                          ? lem_bag_swap (set xs i x) i (i-1)
                        === toBag (set xs i x) 
                   )
    | otherwise = ()
  where 
    a = A.get xs (i-1)

--------------------------------------------------------------------------------
-- | Implementations
--------------------------------------------------------------------------------    

-- Given xs[0..i] sorted and xs[i] doesn't matter, insert x so that xs[0..i+1] is sorted.
{-@ insert :: xs:_ -> x:_  -> { i:Nat | i < A.size xs }
           -> { ys:_ | ys == insert_func xs x i &&    
                       left xs == left ys && right xs == right ys &&
                       A.size ys == A.size xs && token xs == token ys } / [i] @-} 
insert :: Ord a => A.Array a -> a -> Int -> A.Array a                    
insert !xs !x 0 = A.set xs 0 x        
insert !xs !x !i =                 -- sort the element at offset i into the first i+1 elements
  let (!(Ur a), !xs') = A.get2 xs (i-1) -- a is above xs[0..i-1], insert must preserve
  in if x < a
     then let !xs''  = A.set xs' i a        
              !xs''' = insert xs''  x (i - 1)
           in xs''' 
     else A.set xs' i x                    
     
{-@ isort :: { xs:_ | A.size xs > 1 }  
      -> { i:Nat | i <= A.size xs && isSortedBtw xs 0 i }
      -> { ys:_ | toBag xs == toBag ys   && isSorted' ys &&
                  left xs == left ys && right xs == right ys &&
                  A.size xs == A.size ys && token xs == token ys } / [A.size xs - i] @-}
isort :: Ord a => A.Array a -> Int -> A.Array a -- | Sort in-place.
isort xs i = 
  let (s, xs') = A.size2 xs in
  if i == s then xs'
  else
    let !(Ur a, xs'') = A.get2  xs' i
    in isort (insert xs'' a i ? lem_insert_func_sorted xs a i)
              (i+1) 
      ? lem_insert_func_equiv xs a i
      ? lem_bag_unchanged     xs   i

{-@ isort_top' :: { xs:_ | A.size xs > 1 } 
      -> { ys:_ | toBag xs == toBag ys &&  isSorted' ys &&
                  left xs == left ys && right xs == right ys &&
                  A.size xs == A.size ys && token xs == token ys } @-}
isort_top' :: Ord a => A.Array a -> A.Array a
isort_top' xs = isort xs 0

-- | Sort a copy of the input array. Therefore token is not preserved.
{-@ isort_top :: { xs:_ | A.size xs > 1 } 
      -> { ys:_ | toBag xs  == toBag ys  && isSorted' ys &&
                  A.size xs == A.size ys } @-}
isort_top :: Ord a => A.Array a -> A.Array a
isort_top xs0 = let (n, xs1) = A.size2 xs0 in
    if n <= 1 then xs1 
    else let (Ur hd, xs2) = A.get2 xs1 0
             {-@ promise :: { tmp:(Array a) | size tmp == n } 
                         -> { out:(Ur (Array a)) | size (unur out) == n && 
                                                   toSlice (unur out) 0 n == toSlice xs2 0 n} @-}
             promise tmp = Ur (A.copy xs2 0 tmp 0 n)
                         ? lem_copy_equal_slice  xs2 0 tmp 0 n
             {-@ cpy :: { ys:(Array a) | size ys == n && toSlice ys 0 n == toSlice xs2 0 n } @-}  
             Ur cpy = A.alloc n hd (Unsafe.toLinear promise)
          in isort (cpy ? lem_equal_slice_bag   xs2   cpy 0 n) 0
