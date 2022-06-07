{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}
-- {-@ LIQUID "--checks=lma_msort_eq" @-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}

module LinearMerge where

import           Prelude 
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import           Array
import           Order
import           Equivalence
import           Language.Haskell.Liquid.Bag as B
--import           Control.Parallel (par, pseq)

#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
#else
import           Array.List as A
#endif

-- 11 min compilation

{-@ reflect par @-}
par :: a -> b -> b
par _ y = y

{-@ reflect pseq @-}
pseq :: a -> b -> b
pseq _ y = y

--------------------------------------------------------------------------------
-- | Implementations
--------------------------------------------------------------------------------

-- merging the first n,m indices of xs, ys
{-@ reflect merge @-}
{-@ merge :: xs:_ -> ys:_ -> zs:{(A.size zs) = ((A.size xs) + (A.size ys))} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | v <= A.size ys} 
      -> ws:{(A.size ws) == (A.size zs)} / [m+n] @-}
merge :: Ord a => Array a -> Array a -> Array a -> Int -> Int -> Array a
merge _  _  zs 0 0 = zs
merge xs ys zs n 0 = 
  let 
    (a,xs') = (A.get2 xs (n-1))
    zs'     = (set zs (n-1) a) 
  in (merge xs' ys zs' (n-1) 0)
merge xs ys zs 0 m = 
  let 
    (a,ys') = (A.get2 ys (m-1))
    zs' = (set zs (m-1) a) 
  in (merge xs ys' zs' 0 (m-1))
merge xs ys zs n m | xs_n <= ys_m = let zs' = set zs (m+n-1) ys_m
                                    in merge xs' ys' zs' n (m-1)
                   | otherwise    = let zs' = set zs (m+n-1) xs_n
                                    in merge xs' ys' zs' (n-1) m
                      where 
                        (xs_n, xs') = A.get2 xs (n-1)
                        (ys_m, ys') = A.get2 ys (m-1)

{-
// JL: inplace c style of the above merge method. 
// zs is the output buffer
void merge(int* xs, int* ys, int* zs, int n, int m){
  if(n==0 && m==0){
    return;
  }
  if(m == 0){
    int a = xs[n-1];
    zs[n-1] = a;
    merge(xs,ys,zs,n-1,0);
    return;
  }
  if(n == 0){
    int a = ys[m-1];
    zs[m-1] = a;
    merge(xs,ys,zs,0,m-1);
    return;
  }
  int xs_n = xs[n-1];
  int ys_m = yz[m-1];
  if(xs_n <= ys_m){
    zs[m+n-1] = ys_m;
    merge(xs,ys,zs,n,m-1);
    return;
  }else{
    zs[m+n-1] = xs_n;
    merge(xs,ys,zs,n-1,m);
    return;
  }
}
-}

{-@ reflect sort2 @-}
{-@ sort2 :: xs:{A.size xs == 2} -> ys:{(A.size ys == 2)} @-}
sort2 :: Ord a => Array a -> Array a
sort2 xs | a > b     = A.set (A.set xs'' 0 b) 1 a
         | otherwise = xs''
            where 
              (a,xs')  = A.get2 xs  0
              (b,xs'') = A.get2 xs' 1

{-@ reflect sort3 @-}
{-@ sort3 :: xs:{A.size xs == 3} -> ys:{(A.size ys == 3)} @-}
sort3 :: Ord a => Array a -> Array a
sort3 xs | a >  b && b <= c && a <= c = A.set (A.set xs''' 0 b) 1 a
         | a <= b && b >  c && a <= c = A.set (A.set xs''' 1 c) 2 b
        --  | a >  b && b >  c && a <= c = A.set (A.set xs''' 1 c) 2 b
        --  | a <= b && b <= c && a > c = A.set (A.set xs''' 1 c) 2 b
         | a >  b && b <= c && a >  c = A.set (A.set (A.set xs''' 0 b) 1 c) 2 a
         | a <= b && b >  c && a >  c = A.set (A.set (A.set xs''' 0 c) 1 a) 2 b
         | a >  b && b >  c && a >  c = A.set (A.set xs''' 0 c) 2 a
         | otherwise = xs'''
            where 
              (a,xs')   = A.get2 xs   0
              (b,xs'')  = A.get2 xs'  1
              (c,xs''') = A.get2 xs'' 2


-- {-@ reflect sort3 @-}
-- {-@ sort3 :: xs:{A.size xs == 3} -> ys:{(A.size ys == 3)} @-}
-- sort3 :: Ord a => Array a -> Array a
-- sort3 xs = if (a > b) then A.set (A.set xs'' 0 b) 1 a

--             where 
--               (a,xs')   = A.get2 xs   0
--               (b,xs'')  = A.get2 xs'  1
--               (c,xs''') = A.get2 xs'' 2


-- {-@ reflect msort4 @-}
{-@ msort4 :: xs:_ -> ys:{(A.size ys == A.size xs)} -> zs:{(A.size ys == A.size zs) && isSorted zs} / [A.size xs] @-}
msort4 :: Ord a => Array a -> Array a -> Array a
msort4 xs' ys | s == 0 = xs
              | s == 1 = xs
              | s == 2 = sort2 xs ? lma_sort2 xs'
              | s == 3 = sort3 xs ? lma_sort3 xs'
              | otherwise = let
                              qtr = mydiv4 s
                              (rA, xs1)  = A.slice2 xs  0       qtr
                              (rB, xs2)  = A.slice2 xs1 qtr     (2*qtr)
                              (rC, xs3)  = A.slice2 xs2 (2*qtr) (3*qtr)
                              (rD, xs4)  = A.slice2 xs3 (3*qtr) s
                              (tA, ys1)  = A.slice2 ys  0       qtr
                              (tB, ys2)  = A.slice2 ys1 qtr     (2*qtr)
                              (tC, ys3)  = A.slice2 ys2 (2*qtr) (3*qtr)
                              (tD, ys4)  = A.slice2 ys3 (3*qtr) s
                              (tL, ys5)  = A.slice2 ys4 0       (2*qtr)
                              (tR, _  )  = A.slice2 ys5 (2*qtr) s
                              rA' = msort4 rA tA
                              rB' = msort4 rB tB
                              rC' = msort4 rC tC
                              rD' = msort4 rD tD
                              tL' = merge rA' rB' tL qtr qtr ? (lma_merge rA' rB' tL qtr qtr)
                              tR' = merge rC' rD' tR qtr (s-3*qtr) ? (lma_merge rC' rD' tR qtr (s-3*qtr))
                            in 
                              --  rA' `par` rB' `par` rC' `par` rD' `pseq`
                              --  tL' `par` tR' `pseq`
                               merge tL' tR' xs4 (2*qtr) (s-2*qtr) ? (lma_merge tL' tR' xs (2*qtr) (s-2*qtr))
                where 
                  (s,xs) = A.size2 xs'

                            

{- @ reflect topMSort @-}
-- {-@ topMSort :: xs:_ -> ys:{(A.size ys == A.size xs) && isSorted ys} @-}
{-@ topMSort :: xs:_ -> ys:{(A.size ys == A.size xs) } @-}
topMSort :: Ord a => Array a -> Array a
topMSort xs | (s == 0)  = xs'  -- ? isSortedFstN xs 0
            | otherwise = let 
                            (a, xs'') = (A.get2 xs' 0)
                            tmp = make s a
                          -- in msort xs' tmp ? lma_msort xs tmp
                          in msort4 xs'' tmp
                where 
                  (s, xs') = (A.size2 xs)
                
-- mydiv n = div n 2
{-@ reflect mydiv4 @-}
{-@ mydiv4 :: n:{n >= 4} -> m:{v:Nat | (v > 0 && v < n && 4*v <= n)} @-} -- && 4*m <= n
mydiv4 :: Int -> Int
mydiv4 4 = 1
mydiv4 5 = 1 
mydiv4 6 = 1 
mydiv4 7 = 1 
mydiv4 n = 1 + (mydiv4 (n-4))

--------------------------------------------------------------------------------
-- | Proofs for Sortedness
--------------------------------------------------------------------------------

{-@ lma_sort2 :: xs:{ A.size xs == 2 } 
      -> { isSorted (sort2 xs) } @-}
lma_sort2 :: Ord a => Array a -> Proof
lma_sort2 xs  
  | a > b     
    = isSortedFstN (sort2 xs) 2 
    -- === isSortedFstN zs 2 
    -- === (A.get zs 0 <= A.get zs 1)
      ? (lma_gns ys 1 0 a) ? (lma_gs xs 0 b) ? (lma_gs ys 1 a)
    -- === (b <= a)
    -- === True
    *** QED
  | otherwise 
    = isSortedFstN (sort2 xs) 2 
    -- === isSortedFstN xs 2 
    -- === (a <= b)
    -- === True
    *** QED
      where 
        a = A.get xs 0
        b = A.get xs 1
        ys = A.set xs 0 b
        -- zs = A.set ys 1 a

{-@ assume lma_sort3 :: xs:{ A.size xs == 3 } 
      -> { isSorted (sort3 xs) } @-}
lma_sort3 :: Ord a => Array a -> Proof
lma_sort3 _ = ()

{-@ lma_merge_fix :: xs:_-> ys:_ -> zs:{(A.size zs) = ((A.size xs) + (A.size ys))} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | v <= A.size ys} -> l:{v:Nat | l >= n+m && v < A.size zs} 
      -> { A.get (merge xs ys zs n m) l = A.get zs l } / [n+m] @-}
lma_merge_fix ::  Ord a => Array a -> Array a -> Array a -> Int -> Int -> Int -> Proof
lma_merge_fix _  _  _  0 0 _ = ()
lma_merge_fix xs ys zs n 0 l 
  = A.get (merge xs ys zs n 0) l
  -- === A.get (merge xs ys zs' (n-1) 0) l
    ? (lma_merge_fix xs ys zs' (n-1) 0 l)
  -- === A.get zs' l
    ? (lma_gns zs (n-1) l (A.get xs (n-1)))
  === A.get zs l
  *** QED
    where 
      zs' = set zs (n-1) (A.get xs (n-1))
lma_merge_fix xs ys zs 0 m l 
  = A.get (merge xs ys zs 0 m) l
  -- === A.get (merge xs ys zs' 0 (m-1)) l
    ? (lma_merge_fix xs ys zs' 0 (m-1) l)
  -- === A.get zs' l
    ? (lma_gns zs (m-1) l (A.get ys (m-1)))
  === A.get zs l
  *** QED
    where 
      zs' = set zs (m-1) (A.get ys (m-1))
lma_merge_fix xs ys zs n m l 
  | xs_n <= ys_m 
    = let zs' = set zs (m+n-1) ys_m 
      in A.get (merge xs ys zs n m) l
      -- === A.get (merge xs ys zs' n (m-1)) l
        ? (lma_merge_fix xs ys zs' n (m-1) l)
      -- === A.get zs' l
        ? (lma_gns zs (m+n-1) l ys_m)
      === A.get zs l
      *** QED
  | otherwise
    = let zs' = set zs (m+n-1) xs_n 
      in A.get (merge xs ys zs n m) l
      -- === A.get (merge xs ys zs' (n-1) m) l
        ? (lma_merge_fix xs ys zs' (n-1) m l)
      -- === A.get zs' l
        ? (lma_gns zs (m+n-1) l xs_n)
      === A.get zs l
      *** QED
        where 
          xs_n = A.get xs (n-1)
          ys_m = A.get ys (m-1) 


{-@ lma_merge_max :: xs:{isSorted xs} -> ys:{isSorted ys} -> zs:{(A.size zs) = ((A.size xs) + (A.size ys))} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | v <= A.size ys && (n+m) > 0} -> z:{  ((m > 0) => (z >= (A.get ys (m-1)))) && ((n > 0) => (z >= (A.get xs (n-1))))}
      -> { z >= A.get (merge xs ys zs n m) (n+m-1) } / [A.size zs]@-}
lma_merge_max ::  Ord a => Array a -> Array a -> Array a -> Int -> Int -> a -> Proof
lma_merge_max xs ys zs n 0 z
  = z 
  =>= xs_n
    ? lma_gs zs (n-1) xs_n
  -- === A.get zs' (n-1)
    ? (lma_merge_fix xs ys zs' (n-1) 0 (n-1))
  -- === A.get (merge xs ys zs' (n-1) 0) (n-1)
  === A.get (merge xs ys zs n 0) (n-1)
  *** QED
    where 
      zs'  = set zs (n-1) xs_n
      xs_n = A.get xs (n-1)
lma_merge_max xs ys zs 0 m z 
  = z
  =>= ys_m
    ? lma_gs zs (m-1) ys_m
  -- === A.get zs' (m-1)
    ? (lma_merge_fix xs ys zs' 0 (m-1) (m-1))
  -- === A.get (merge xs ys zs' 0 (m-1)) (m-1)
  === A.get (merge xs ys zs 0 m) (m-1)
  *** QED
    where 
      zs'  = set zs (m-1) ys_m
      ys_m = A.get ys (m-1)
lma_merge_max xs ys zs n m z 
  | xs_n <= ys_m 
    = let 
        zs' = set zs (m+n-1) ys_m 
      in z
      =>= ys_m
        ? (lma_gs zs (m+n-1) ys_m)
      -- === A.get zs' (m+n-1)
        ? (lma_merge_fix xs ys zs' n (m-1) (m+n-1)) 
      -- === A.get (merge xs ys zs' n (m-1)) (m+n-1)
      === A.get (merge xs ys zs n m) (m+n-1)
      *** QED
  | otherwise
    = let 
        zs' = set zs (m+n-1) xs_n 
      in z
      =>= xs_n
        ? (lma_gs zs (m+n-1) xs_n)
      -- === A.get zs' (m+n-1)
        ? (lma_merge_fix xs ys zs' (n-1) m (m+n-1)) 
      -- === A.get (merge xs ys zs' (n-1) m) (m+n-1)
      === A.get (merge xs ys zs n m) (m+n-1)
      *** QED
        where 
          xs_n = A.get xs (n-1)
          ys_m = A.get ys (m-1)

-- Commenting out intermediate steps greatly reduces the runtime (12'5 -> 3'53)
-- showing the output of merge is sorted if the inputs are sorted
{-@ lma_merge :: xs:{isSorted xs} -> ys:{isSorted ys} -> zs:{(A.size zs) = ((A.size xs) + (A.size ys))} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | v <= A.size ys} 
      -> { isSortedFstN (merge xs ys zs n m) (n+m)} / [n+m]@-}
lma_merge :: Ord a => Array a -> Array a -> Array a -> Int -> Int -> Proof
-- -- lma_merge [] ys _ _ = ()
lma_merge _  _  _  0 0 = ()
lma_merge _  _  _  0 1 = ()
lma_merge _  _  _ 1 0 = ()
lma_merge xs ys zs n 0
  = isSortedFstN mer1 n
  -- === (((A.get mer1 (n-2)) <= (A.get mer1 (n-1))) && (isSortedFstN mer1 (n-1)))
  -- === (((A.get mer2 (n-2)) <= (A.get mer2 (n-1))) && (isSortedFstN mer2 (n-1)))
    ? (lma_merge_fix xs ys zs' (n-1) 0 (n-1)) ? (lma_gs zs (n-1) xs_n)
  -- === (((A.get mer2 (n-2)) <= xs_n) && (isSortedFstN mer2 (n-1)))
    ? (lma_merge_max xs ys zs' (n-1) 0 (xs_n ? lma_is_isfn xs n)) -- Does not work with lma_is_isfn xs n
  -- === (isSortedFstN mer2 (n-1))
    ? (lma_merge xs ys zs' (n-1) 0)
  === True
  *** QED
    where 
      mer1 = merge xs ys zs n 0
      -- mer2 = merge xs ys zs' (n-1) 0
      zs'  = set zs (n-1) xs_n
      xs_n = A.get xs (n-1)
lma_merge xs ys zs 0 m 
  = isSortedFstN mer1 m
  -- === (((A.get mer1 (m-2)) <= (A.get mer1 (m-1))) && (isSortedFstN mer1 (m-1)))
  -- === (((A.get mer2 (m-2)) <= (A.get mer2 (m-1))) && (isSortedFstN mer2 (m-1)))
    ? (lma_merge_fix xs ys zs' 0 (m-1) (m-1)) ? (lma_gs zs (m-1) ys_m)
  -- === (((A.get mer2 (m-2)) <= ys_m) && (isSortedFstN mer2 (m-1)))
    ? (lma_merge_max xs ys zs' 0 (m-1) (ys_m ? lma_is_isfn ys m)) -- lma_is_isfn ys m
  -- === (isSortedFstN mer2 (m-1))
    ? (lma_merge xs ys zs' 0 (m-1))
  === True
  *** QED
    where 
      mer1 = merge xs ys zs 0 m
      -- mer2 = merge xs ys zs' 0 (m-1)
      zs'  = set zs (m-1) ys_m
      ys_m = A.get ys (m-1)
lma_merge xs ys zs n m
  | xs_n <= ys_m 
    = let 
        zs' = set zs (n+m-1) ys_m 
        -- mer2 = merge xs ys zs' n (m-1)
      in isSortedFstN mer1 (n+m)
      -- === (((A.get mer1 (n+m-2)) <= (A.get mer1 (n+m-1))) && (isSortedFstN mer1 (n+m-1)))
      -- === (((A.get mer2 (n+m-2)) <= (A.get mer2 (n+m-1))) && (isSortedFstN mer2 (n+m-1)))
        ? (lma_merge_fix xs ys zs' n (m-1) (n+m-1)) ? (lma_gs zs (n+m-1) ys_m)
      -- === (((A.get mer2 (n+m-2)) <= ys_m) && (isSortedFstN mer2 (n+m-1)))
        ? (lma_merge_max xs ys zs' n (m-1) (ys_m ? lma_is_isfn ys m))
      -- === (isSortedFstN mer2 (n+m-1))
        ? (lma_merge xs ys zs' n (m-1))
      === True
      *** QED
  | otherwise 
    = let 
        zs' = set zs (n+m-1) xs_n 
        -- mer2 = merge xs ys zs' (n-1) m
      in isSortedFstN mer1 (n+m)
      -- === (((A.get mer1 (n+m-2)) <= (A.get mer1 (n+m-1))) && (isSortedFstN mer1 (n+m-1)))
      -- === (((A.get mer2 (n+m-2)) <= (A.get mer2 (n+m-1))) && (isSortedFstN mer2 (n+m-1)))
        ? (lma_merge_fix xs ys zs' (n-1) m (n+m-1)) ? (lma_gs zs (n+m-1) xs_n)
      -- === (((A.get mer2 (n+m-2)) <= xs_n) && (isSortedFstN mer2 (n+m-1)))
        ? (lma_merge_max xs ys zs' (n-1) m (xs_n ? lma_is_isfn xs n))
      -- === (isSortedFstN mer2 (n+m-1))
        ? (lma_merge xs ys zs' (n-1) m)
      === True
      *** QED
        where
          mer1 = merge xs ys zs n m
          xs_n = A.get xs (n-1)
          ys_m = A.get ys (m-1)


{-@ lma_merge_eq :: xs:_ -> ys:_ -> zs:{(A.size zs) == ((A.size xs) + (A.size ys))} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | v <= A.size ys} 
      -> {toBagLeft (merge xs ys zs n m) (n+m) == B.union (toBagLeft xs n) (toBagLeft ys m)} / [m+n] @-}
lma_merge_eq :: Ord a => Array a -> Array a -> Array a -> Int -> Int -> Proof
lma_merge_eq xs ys zs 0 0 = ()
lma_merge_eq xs ys zs n 0 
  = toBagLeft (merge xs ys zs n 0) n
  -- === toBagLeft mer2 n
  -- === B.union (S.singleton (get mer2 (n-1))) (toBagLeft mer2 (n-1))
    ? (lma_merge_eq xs ys zs' (n-1) 0)
  -- === B.union (S.singleton (get mer2 (n-1))) (B.union (toBagLeft xs (n-1)) (toBagLeft ys 0))
  -- === B.union (toBagLeft ys 0) (B.union (S.singleton (get mer2 (n-1))) (toBagLeft xs (n-1)))
    ? (lma_merge_fix xs ys zs' (n-1) 0 (n-1)) ? (lma_gs zs (n-1) xs_n)
  -- === B.union (toBagLeft ys 0) (B.union (S.singleton xs_n) (toBagLeft xs (n-1)))
  === B.union (toBagLeft ys 0) (toBagLeft xs n)
  *** QED
    where 
      xs_n = A.get xs (n-1)
      zs'  = set zs (n-1) xs_n
      mer2 = merge xs ys zs' (n-1) 0
lma_merge_eq xs ys zs 0 m
  = toBagLeft (merge xs ys zs 0 m) m
  -- === toBagLeft mer2 m
  -- === B.union (S.singleton (get mer2 (m-1))) (toBagLeft mer2 (m-1))
    ? (lma_merge_eq xs ys zs' 0 (m-1))
  -- === B.union (S.singleton (get mer2 (m-1))) (B.union (toBagLeft ys (m-1)) (toBagLeft xs 0))
  -- === B.union (toBagLeft xs 0) (B.union (S.singleton (get mer2 (m-1))) (toBagLeft ys (m-1)))
    ? (lma_merge_fix xs ys zs' 0 (m-1) (m-1)) ? (lma_gs zs (m-1) ys_m)
  -- === B.union (toBagLeft xs 0) (B.union (S.singleton ys_m) (toBagLeft ys (m-1)))
  === B.union (toBagLeft xs 0) (toBagLeft ys m)
  *** QED
    where 
      ys_m = A.get ys (m-1)
      zs'  = set zs (m-1) ys_m
      mer2 = merge xs ys zs' 0 (m-1)
lma_merge_eq xs ys zs n m 
  | xs_n <= ys_m 
    = let 
        zs' = set zs (m+n-1) ys_m 
        mer2 = merge xs ys zs' n (m-1)
      in toBagLeft (merge xs ys zs n m) (n+m)
      -- === toBagLeft mer2 (n+m)
      -- === B.union (S.singleton (get mer2 (n+m-1))) (toBagLeft mer2 (n+m-1))
        ? (lma_merge_eq xs ys zs' n (m-1))
      -- === B.union (S.singleton (get mer2 (n+m-1))) (B.union (toBagLeft xs n) (toBagLeft ys (m-1)))
      -- === B.union (toBagLeft xs n) (B.union (S.singleton (get mer2 (n+m-1))) (toBagLeft ys (m-1)))
        ? (lma_merge_fix xs ys zs' n (m-1) (n+m-1)) ? (lma_gs zs (n+m-1) ys_m)
      -- === B.union (toBagLeft xs n) (B.union (S.singleton ys_m) (toBagLeft ys (m-1)))
      === B.union (toBagLeft xs n) (toBagLeft ys m)
      *** QED
  | otherwise
    = let 
        zs' = set zs (m+n-1) xs_n 
        mer2 = merge xs ys zs' (n-1) m
      in toBagLeft (merge xs ys zs n m) (n+m)
      -- === toBagLeft mer2 (n+m)
      -- === B.union (S.singleton (get mer2 (n+m-1))) (toBagLeft mer2 (n+m-1))
        ? (lma_merge_eq xs ys zs' (n-1) m)
      -- === B.union (S.singleton (get mer2 (n+m-1))) (B.union (toBagLeft xs (n-1)) (toBagLeft ys m))
      -- === B.union (toBagLeft ys m) (B.union (S.singleton (get mer2 (n+m-1))) (toBagLeft xs (n-1)))
        ? (lma_merge_fix xs ys zs' (n-1) m (n+m-1)) ? (lma_gs zs (n+m-1) xs_n)
      -- === B.union (toBagLeft ys m) (B.union (S.singleton xs_n) (toBagLeft xs (n-1)))
      === B.union (toBagLeft ys m) (toBagLeft xs n)
      *** QED
        where
          xs_n = A.get xs (n-1)
          ys_m = A.get ys (m-1)