{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}
-- {-@ LIQUID "--checks=lma_msort_eq" @-}


-- {-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module LinearMerge where

import           Prelude 
import           Language.Haskell.Liquid.ProofCombinators
import qualified Data.Set as S
import           Array as A
import           Order
import           Equivalence
-- import           Language.Haskell.Liquid.Bag as B

-- 11 min compilation

--------------------------------------------------------------------------------
-- | Implementations
--------------------------------------------------------------------------------
 
-- >>>  merge [1:3:4:6] [2:5] 4 2
--

-- merging the first n,m indices of xs, ys
{-@ reflect merge @-}
{-@ merge :: xs:_ -> ys:_ -> zs:{(A.size zs) = ((A.size xs) + (A.size ys))} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | v <= A.size ys} 
      -> ws:{(A.size ws) = (A.size zs)} / [m+n] @-}
merge :: Ord a => Array a -> Array a -> Array a -> Int -> Int -> Array a
merge xs ys zs 0 0 = zs
merge xs ys zs n 0 = let zs' = (set zs (n-1) (A.get xs (n-1))) in (merge xs ys zs' (n-1) 0)
merge xs ys zs 0 m = let zs' = (set zs (m-1) (A.get ys (m-1))) in (merge xs ys zs' 0 (m-1))
merge xs ys zs n m | xs_n <= ys_m = let zs' = set zs (m+n-1) ys_m 
                                    in merge xs ys zs' n (m-1)
                                    -- let zs' = merge xs ys zs (n) (m-1)   
                                    -- in (set zs' (m+n-1) ys_m)

                   | otherwise    = let zs' = set zs (m+n-1) xs_n
                                    in merge xs ys zs' (n-1) m
                                    -- let zs' = merge xs ys zs (n-1) (m) 
                                    -- in (set zs' (m+n-1) xs_n)
                      where 
                        xs_n = A.get xs (n-1)
                        ys_m = A.get ys (m-1) 


-- >>>  LinearMerge.msort ([1,3,2,9,6,0,5,2,10,-1]) ([0,0,0,0,0,0,0,0,0,0])
-- [-1,0,1,2,2,3,5,6,9,10]
-- TODO: Inefficient implementation 
-- need to show xs == ys 
{-@ reflect msort @-}
{-@ msort :: xs:_ -> ys:{(A.size ys == A.size xs)} -> zs:{(A.size ys == A.size zs)} / [A.size xs] @-}
msort :: Ord a => Array a -> Array a -> Array a
msort xs ys | (A.size xs) == 0 = xs
            | (A.size xs) == 1 = xs
            | otherwise      = let  
                                  yls' = (msort xls yls)
                                  yrs' = (msort xrs yrs)
                                  (xls, xrs) = splitMid xs
                                  (yls, yrs) = splitMid ys
                                in merge yls' yrs' xs (A.size yls') (A.size yrs')

{-@ reflect topMSort @-}
{-@ topMSort :: xs:_ -> ys:{(A.size ys == A.size xs)} @-}
topMSort :: Ord a => Array a -> Array a
topMSort xs | (A.size xs == 0) = xs
            | otherwise      = let 
                                  tmp = make (A.size xs) (A.get xs 0)
                               in msort xs tmp

{-@ reflect splitMid @-}
{-@ splitMid :: xs:{A.size xs >= 2} -> {t:_ | ((A.size (fst t)) < (A.size xs) && (A.size (snd t)) < (A.size xs)) && (A.size xs = (A.size (fst t)) + (A.size (snd t))) && ((A.size (fst t)) = (mydiv (A.size xs)))} @-}
splitMid :: Array a -> (Array a, Array a)
splitMid xs = ((subArray xs 0 m), (subArray xs m n)) 
  where 
    n = A.size xs 
    m = mydiv n


-- mydiv n = div n 2
{-@ reflect mydiv @-}
{-@ mydiv :: n:{n >= 2} -> m:{v:Nat | (v > 0 && v < n)} @-}
mydiv :: Int -> Int
mydiv 2 = 1
mydiv 3 = 1 
mydiv n = 1 + (mydiv (n-2))


--------------------------------------------------------------------------------
-- | Proofs for Sortedness
--------------------------------------------------------------------------------

{-@ lma_merge_fix :: xs:_-> ys:_ -> zs:{(A.size zs) = ((A.size xs) + (A.size ys))} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | v <= A.size ys} -> l:{v:Nat | l >= n+m && v < A.size zs} 
      -> { A.get (merge xs ys zs n m) l = A.get zs l } / [n+m] @-}
lma_merge_fix ::  Ord a => Array a -> Array a -> Array a -> Int -> Int -> Int -> Proof
lma_merge_fix xs ys zs 0 0 _ = ()
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



-- TODO: I really want to A.get rid of the edge cases where n-1 can be -1
-- FIXME: constrains z >= (A.get xs (n-1)) does not enforce n > 0, but it makes the program into a loop
--        nor does it check the constrain of n when i am calling this method, another loop
-- n = 0 implies  -- TODO: Forever loop, Not working
{-@ lma_merge_max :: xs:{isSorted xs} -> ys:{isSorted ys} -> zs:{(A.size zs) = ((A.size xs) + (A.size ys))} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | v <= A.size ys && (n+m) > 0} -> z:{  ((m > 0) => (z >= (A.get ys (m-1)))) && ((n > 0) => (z >= (A.get xs (n-1))))}
      -> { z >= A.get (merge xs ys zs n m) (n+m-1) } / [A.size zs]@-}
-- {-@ lma_merge_max :: xs:{isSorted xs} -> ys:{isSorted ys} -> zs:{(A.size zs) = ((A.size xs) + (A.size ys))} -> n:{v:Nat | v > 0 && v <= A.size xs} -> m:{v:Nat | v > 0 && v <= A.size ys} -> z:{  z >= (A.get xs (n-1)) && z >= (A.get ys (m-1))} 
--       -> { z >= A.get (merge xs ys zs n m) (n+m-1) } @-}
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
-- TODO: Interesting observation: one less line of proof increase the compile time by 1/5 (from 100s to 80s)
{-@ lma_merge :: xs:{isSorted xs} -> ys:{isSorted ys} -> zs:{(A.size zs) = ((A.size xs) + (A.size ys))} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | v <= A.size ys} 
      -> { isSortedFstN (merge xs ys zs n m) (n+m)} / [n+m]@-}
lma_merge :: Ord a => Array a -> Array a -> Array a -> Int -> Int -> Proof
-- -- lma_merge [] ys _ _ = ()
lma_merge xs ys zs 0 0 = ()
lma_merge xs ys zs 0 1 = ()
lma_merge xs ys zs 1 0 = ()
lma_merge xs ys zs n 0
  = isSortedFstN mer1 n
  -- === (((A.get mer1 (n-2)) <= (A.get mer1 (n-1))) && (isSortedFstN mer1 (n-1)))
  -- === (((A.get mer2 (n-2)) <= (A.get mer2 (n-1))) && (isSortedFstN mer2 (n-1)))
    ? (lma_merge_fix xs ys zs' (n-1) 0 (n-1)) &&& (lma_gs zs (n-1) xs_n)
  -- === (((A.get mer2 (n-2)) <= xs_n) && (isSortedFstN mer2 (n-1)))
    ? (lma_merge_max xs ys zs' (n-1) 0 (xs_n ? lma_is_isfn xs n))
  -- === (isSortedFstN mer2 (n-1))
    ? (lma_merge xs ys zs' (n-1) 0)
  === True
  *** QED
    where 
      mer1 = merge xs ys zs n 0
      mer2 = merge xs ys zs' (n-1) 0
      zs'  = set zs (n-1) xs_n
      xs_n = A.get xs (n-1)
lma_merge xs ys zs 0 m 
  = isSortedFstN mer1 m
  -- === (((A.get mer1 (m-2)) <= (A.get mer1 (m-1))) && (isSortedFstN mer1 (m-1)))
  -- === (((A.get mer2 (m-2)) <= (A.get mer2 (m-1))) && (isSortedFstN mer2 (m-1)))
    ? (lma_merge_fix xs ys zs' 0 (m-1) (m-1)) &&& (lma_gs zs (m-1) ys_m)
  -- === (((A.get mer2 (m-2)) <= ys_m) && (isSortedFstN mer2 (m-1)))
    ? (lma_merge_max xs ys zs' 0 (m-1) (ys_m ? lma_is_isfn ys m))
  -- === (isSortedFstN mer2 (m-1))
    ? (lma_merge xs ys zs' 0 (m-1))
  === True
  *** QED
    where 
      mer1 = merge xs ys zs 0 m
      mer2 = merge xs ys zs' 0 (m-1)
      zs'  = set zs (m-1) ys_m
      ys_m = A.get ys (m-1)
lma_merge xs ys zs n m
  | xs_n <= ys_m 
    = let 
        zs' = set zs (n+m-1) ys_m 
        mer2 = merge xs ys zs' n (m-1)
      in isSortedFstN mer1 (n+m)
      -- === (((A.get mer1 (n+m-2)) <= (A.get mer1 (n+m-1))) && (isSortedFstN mer1 (n+m-1)))
      -- === (((A.get mer2 (n+m-2)) <= (A.get mer2 (n+m-1))) && (isSortedFstN mer2 (n+m-1)))
        ? (lma_merge_fix xs ys zs' n (m-1) (n+m-1)) &&& (lma_gs zs (n+m-1) ys_m)
      -- === (((A.get mer2 (n+m-2)) <= ys_m) && (isSortedFstN mer2 (n+m-1)))
        ? (lma_merge_max xs ys zs' n (m-1) (ys_m ? lma_is_isfn ys m))
      -- === (isSortedFstN mer2 (n+m-1))
        ? (lma_merge xs ys zs' n (m-1))
      === True
      *** QED
  | otherwise 
    = let 
        zs' = set zs (n+m-1) xs_n 
        mer2 = merge xs ys zs' (n-1) m
      in isSortedFstN mer1 (n+m)
      -- === (((A.get mer1 (n+m-2)) <= (A.get mer1 (n+m-1))) && (isSortedFstN mer1 (n+m-1)))
      -- === (((A.get mer2 (n+m-2)) <= (A.get mer2 (n+m-1))) && (isSortedFstN mer2 (n+m-1)))
        ? (lma_merge_fix xs ys zs' (n-1) m (n+m-1)) &&& (lma_gs zs (n+m-1) xs_n)
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


{-@ lma_msort :: xs:_ -> ys:{(A.size ys == A.size xs)}
      -> { isSortedFstN (msort xs ys) (A.size xs)} / [A.size xs] @-}
lma_msort ::  Ord a => Array a ->  Array a -> Proof
lma_msort xs ys
  | (A.size xs == 0) = ()
  | (A.size xs == 1) = ()
  | otherwise      =
    let 
      yls' = (msort xls yls)
      yrs' = (msort xrs yrs)
      (xls, xrs) = splitMid xs
      (yls, yrs) = splitMid ys
      n = (A.size xs)
    in
      isSortedFstN (msort xs ys) n
      -- === isSortedFstN (merge yls' yrs' xs (A.size yls') (A.size yrs')) n
        ? (lma_merge (yls' ? (lma_msort xls yls)) (yrs' ? (lma_msort xrs yrs)) xs (A.size yls') (A.size yrs'))
      === True
      *** QED

{-@ lma_topMSort :: xs:_ 
      -> { isSorted (topMSort xs) } / [A.size xs] @-}
lma_topMSort ::  Ord a => Array a ->  Proof
lma_topMSort xs
  | (A.size xs == 0) = ()
  | otherwise      =
    let 
      tmp = make (A.size xs) (A.get xs 0)
    in
      isSorted (topMSort xs)
      === isSortedFstN (msort xs tmp) (A.size xs)
        ? (lma_msort xs tmp)
      === True
      *** QED


--------------------------------------------------------------------------------
-- | Proofs for Equivalence
--------------------------------------------------------------------------------

-- toSet (merge xs ys zs n m) (n+m) = union (toSet xs n) (toSet ys m)
{-@ lma_merge_eq :: xs:_ -> ys:_ -> zs:{(A.size zs) = ((A.size xs) + (A.size ys))} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | v <= A.size ys} 
      -> {toSet (merge xs ys zs n m) (n+m) = S.union (toSet xs n) (toSet ys m)} / [m+n] @-}
lma_merge_eq :: Ord a => Array a -> Array a -> Array a -> Int -> Int -> Proof
lma_merge_eq xs ys zs 0 0 = ()
lma_merge_eq xs ys zs n 0 
  = toSet (merge xs ys zs n 0) n
  -- === toSet mer2 n
  -- === S.union (S.singleton (get mer2 (n-1))) (toSet mer2 (n-1))
    ? (lma_merge_eq xs ys zs' (n-1) 0)
  -- === S.union (S.singleton (get mer2 (n-1))) (S.union (toSet xs (n-1)) (toSet ys 0))
  -- === S.union (toSet ys 0) (S.union (S.singleton (get mer2 (n-1))) (toSet xs (n-1)))
    ? (lma_merge_fix xs ys zs' (n-1) 0 (n-1)) &&& (lma_gs zs (n-1) xs_n)
  -- === S.union (toSet ys 0) (S.union (S.singleton xs_n) (toSet xs (n-1)))
  === S.union (toSet ys 0) (toSet xs n)
  *** QED
    where 
      xs_n = A.get xs (n-1)
      zs'  = set zs (n-1) xs_n
      mer2 = merge xs ys zs' (n-1) 0
lma_merge_eq xs ys zs 0 m
  = toSet (merge xs ys zs 0 m) m
  -- === toSet mer2 m
  -- === S.union (S.singleton (get mer2 (m-1))) (toSet mer2 (m-1))
    ? (lma_merge_eq xs ys zs' 0 (m-1))
  -- === S.union (S.singleton (get mer2 (m-1))) (S.union (toSet ys (m-1)) (toSet xs 0))
  -- === S.union (toSet xs 0) (S.union (S.singleton (get mer2 (m-1))) (toSet ys (m-1)))
    ? (lma_merge_fix xs ys zs' 0 (m-1) (m-1)) &&& (lma_gs zs (m-1) ys_m)
  -- === S.union (toSet xs 0) (S.union (S.singleton ys_m) (toSet ys (m-1)))
  === S.union (toSet xs 0) (toSet ys m)
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
      in toSet (merge xs ys zs n m) (n+m)
      -- === toSet mer2 (n+m)
      -- === S.union (S.singleton (get mer2 (n+m-1))) (toSet mer2 (n+m-1))
        ? (lma_merge_eq xs ys zs' n (m-1))
      -- === S.union (S.singleton (get mer2 (n+m-1))) (S.union (toSet xs n) (toSet ys (m-1)))
      -- === S.union (toSet xs n) (S.union (S.singleton (get mer2 (n+m-1))) (toSet ys (m-1)))
        ? (lma_merge_fix xs ys zs' n (m-1) (n+m-1)) &&& (lma_gs zs (n+m-1) ys_m)
      -- === S.union (toSet xs n) (S.union (S.singleton ys_m) (toSet ys (m-1)))
      === S.union (toSet xs n) (toSet ys m)
      *** QED
  | otherwise
    = let 
        zs' = set zs (m+n-1) xs_n 
        mer2 = merge xs ys zs' (n-1) m
      in toSet (merge xs ys zs n m) (n+m)
      -- === toSet mer2 (n+m)
      -- === S.union (S.singleton (get mer2 (n+m-1))) (toSet mer2 (n+m-1))
        ? (lma_merge_eq xs ys zs' (n-1) m)
      -- === S.union (S.singleton (get mer2 (n+m-1))) (S.union (toSet xs (n-1)) (toSet ys m))
      -- === S.union (toSet ys m) (S.union (S.singleton (get mer2 (n+m-1))) (toSet xs (n-1)))
        ? (lma_merge_fix xs ys zs' (n-1) m (n+m-1)) &&& (lma_gs zs (n+m-1) xs_n)
      -- === S.union (toSet ys m) (S.union (S.singleton xs_n) (toSet xs (n-1)))
      === S.union (toSet ys m) (toSet xs n)
      *** QED
        where
          xs_n = A.get xs (n-1)
          ys_m = A.get ys (m-1)


{-@ lma_msort_eq :: xs:_  -> ys:{(A.size ys == A.size xs)}
      -> { equalP (msort xs ys) xs } / [A.size xs]@-}
lma_msort_eq :: Ord a => Array a -> Array a -> Proof
lma_msort_eq xs ys 
  | (A.size xs) == 0 = ()
  | (A.size xs) == 1 = ()
  | otherwise
    = let  
        yls' = (msort xls yls)
        yrs' = (msort xrs yrs)
        (xls, xrs) = splitMid xs
        (yls, yrs) = splitMid ys
      in toSet (msort xs ys) (A.size (msort xs ys))
      -- === toSet (msort xs ys) (A.size xs)
      -- === toSet (merge yls' yrs' xs (A.size yls') (A.size yrs')) (A.size xs)
        ? (lma_merge_eq yls' yrs' xs (A.size yls') (A.size yrs'))
      -- === S.union (toSet yls' (A.size yls')) (toSet yrs' (A.size yrs'))
        ? (lma_msort_eq xls yls) &&& (lma_msort_eq xrs yrs)
      -- === S.union (toSet xls (A.size xls)) (toSet xrs (A.size xrs))
        ? (lma_splitMid_eq xs)
      === toSet xs (A.size xs)
      *** QED


-- assume that splitMid does its job, namely the union of the return lists is the toSet of original list
{-@ assume lma_splitMid_eq :: xs:{A.size xs >= 2} 
      -> {S.union (toSet (fst (splitMid xs)) (A.size (fst (splitMid xs)))) (toSet (snd (splitMid xs)) (A.size (snd (splitMid xs)))) = toSet xs (A.size xs)}  @-}
lma_splitMid_eq :: Array a -> Proof
lma_splitMid_eq _ = ()