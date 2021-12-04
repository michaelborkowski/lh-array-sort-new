{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}
-- {-@ LIQUID "--checks=lma_merge_max" @-}


-- {-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module Merge where

import           Prelude
import           Language.Haskell.Liquid.ProofCombinators
import qualified Array as A
import           Order


--------------------------------------------------------------------------------
-- | Implementations
--------------------------------------------------------------------------------
 
-- >>>  merge [1:3:4:6] [2:5] 4 2
--

-- merging the first n,m indices of xs, ys
{-@ reflect merge @-}
{-@ merge :: xs:{A.size xs > 0} -> ys:_ -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | v <= A.size ys} 
      -> zs:{(A.size zs) = ((A.size xs) + (A.size ys))} / [m+n] @-}
merge :: Ord a => A.Array a -> A.Array a -> Int -> Int -> A.Array a
merge xs ys 0 0 = (A.make ((A.size xs)+(A.size ys)) (A.get xs 0))
merge xs ys 0 m = let zs = merge xs ys 0 (m-1) in (A.set zs (m-1) (A.get ys (m-1)))
merge xs ys n 0 = let zs = merge xs ys (n-1) 0 in (A.set zs (n-1) (A.get xs (n-1)))
merge xs ys n m | xs_n <= ys_m = let zs = merge xs ys (n) (m-1)   
                                  in (A.set zs (m+n-1) ys_m)
                | otherwise    = let zs = merge xs ys (n-1) (m) 
                                  in (A.set zs (m+n-1) xs_n)
                  where 
                    xs_n = A.get xs (n-1)
                    ys_m = A.get ys (m-1) 


-- >>>  msort (fromList [1,3,2,9,6,0,5,2,10,-1])
-- [-1,0,1,2,2,3,5,6,9,10]

-- TODO: Inefficient implementation 
-- need to show xs == ys 
{-@ reflect msort @-}
{-@ msort :: xs:_ -> ys:{(A.size ys == A.size xs)} / [A.size xs] @-}
msort :: Ord a => A.Array a -> A.Array a
msort xs | (A.size xs) == 0 = xs
         | (A.size xs) == 1 = xs
         | otherwise      = let  
                              ls' = (msort ls)
                              rs' = (msort rs)
                              (ls, rs) = splitMid xs
                            in merge ls' rs' (A.size ls') (A.size rs')


{-@ reflect splitMid @-}
{-@ splitMid :: xs:{A.size xs >= 2} -> {t:_ | ((A.size (fst t)) < (A.size xs) && (A.size (snd t)) < (A.size xs)) && (A.size xs = (A.size (fst t)) + (A.size (snd t)))} @-}
splitMid :: A.Array a -> (A.Array a, A.Array a)
splitMid xs = ((A.slice xs 0 m), (A.slice xs m n))
  where 
    n = A.size xs 
    m = mydiv n

{-@ reflect subArrayR @-}
{-@ subArrayR :: xs:{A.size xs >= 1} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | n <= m && m <= A.size xs} -> c:{v:Nat | v <= m-n} -> ys:{A.size ys == m-n} / [c]@-}
subArrayR :: A.Array a -> Int -> Int -> Int -> A.Array a
subArrayR xs n m 0 = A.make (m-n) (A.get xs 0)  
subArrayR xs n m c = A.set (subArrayR xs n m (c-1)) (c-1) (A.get xs (n+c-1))

{-@ reflect subArray @-}
{-@ subArray :: xs:{A.size xs >= 1} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | n <= m && m <= A.size xs} -> ys:{A.size ys == m-n}@-}
subArray :: A.Array a -> Int -> Int -> A.Array a
subArray xs n m = subArrayR xs n m (m-n)


-- mydiv n = div n 2
{-@ reflect mydiv @-}
{-@ mydiv :: n:{n >= 2} -> m:{v:Nat | (v > 0 && v < n)} @-}
mydiv :: Int -> Int
mydiv 2 = 1
mydiv 3 = 1 
mydiv n = 1 + (mydiv (n-2))

--------------------------------------------------------------------------------
-- | Proofs
--------------------------------------------------------------------------------

-- TODO: I really want to A.get rid of the edge cases where n-1 can be -1
-- FIXME: constrains z >= (A.get xs (n-1)) does not enforce n > 0, but it makes the program into a loop
--        nor does it check the constrain of n when i am calling this method, another loop
-- n = 0 implies  -- TODO: Forever loop, Not working
-- {-@ lma_merge_max :: xs:{isSorted xs} -> ys:{isSorted ys} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | v > 0 && v <= A.size ys} -> z:{  ((n > 0) => (z >= (A.get xs (n-1)))) && z >= (A.get ys (m-1))}
      -- -> { z >= A.get (merge xs ys n m) (n+m-1) } @-}
{-@ lma_merge_max :: xs:{isSorted xs} -> ys:{isSorted ys} -> n:{v:Nat | v > 0 && v <= A.size xs} -> m:{v:Nat | v > 0 && v <= A.size ys} -> z:{  z >= (A.get xs (n-1)) && z >= (A.get ys (m-1))} 
      -> { z >= A.get (merge xs ys n m) (n+m-1) } @-}
lma_merge_max ::  Ord a => A.Array a -> A.Array a -> Int -> Int -> a -> Proof
-- lma_merge_max xs ys 0 m z 
--   = z
--   =>= ys_m
--     ? A.lma_gs zs (m-1) ys_m
--   === A.get (A.set zs (m-1) ys_m) (m-1)
--   === A.get (merge xs ys 0 m) (m-1)
--   *** QED
--     where 
--       zs  = merge xs ys 0 (m-1)
--       ys_m = A.get ys (m-1)
lma_merge_max xs ys n m z 
  | xs_n <= ys_m 
    = z
    =>= ys_m
      ? A.lma_gs zs (m+n-1) ys_m
    -- === A.get (A.set zs (m+n-1) ys_m) (m+n-1)
    === A.get (merge xs ys n m) (m+n-1)
    *** QED
  | otherwise
    = z
    =>= xs_n
      ? A.lma_gs zs' (m+n-1) xs_n
    -- === A.get (A.set zs' (m+n-1) xs_n) (m+n-1)
    === A.get (merge xs ys n m) (m+n-1)
    *** QED
      where 
        zs  = merge xs ys n (m-1)
        zs' = merge xs ys (n-1) m
        xs_n = A.get xs (n-1)
        ys_m = A.get ys (m-1)

-- TODO: Dumb to write this proof separately, for the case n = 0
{-@ lma_merge_max_m :: xs:{A.size xs > 0} -> ys:{isSorted ys} -> m:{v:Nat | v > 0 && v <= A.size ys} -> z:{ z >= (A.get ys (m-1))}
      -> { z >= A.get (merge xs ys 0 m) (m-1) } @-}
lma_merge_max_m ::  Ord a => A.Array a -> A.Array a -> Int -> a -> Proof
lma_merge_max_m xs ys m z 
  = z
  =>= ys_m
    ? A.lma_gs zs (m-1) ys_m
  -- === A.get (A.set zs (m-1) ys_m) (m-1)
  === A.get (merge xs ys 0 m) (m-1)
  *** QED
    where
      zs  = merge xs ys 0 (m-1)
      ys_m = A.get ys (m-1)

-- TODO: Dumb to write this proof separately, for the case n = 0
{-@ lma_merge_max_n :: xs:{isSorted xs} -> ys:_ -> n:{v:Nat | v > 0 && v <= A.size xs} -> z:{ z >= (A.get xs (n-1))}
      -> { z >= A.get (merge xs ys n 0) (n-1) } @-}
lma_merge_max_n ::  Ord a => A.Array a -> A.Array a -> Int -> a -> Proof
lma_merge_max_n xs ys n z 
  = z
  =>= xs_n
    ? A.lma_gs zs (n-1) xs_n
  -- === A.get (A.set zs (n-1) xs_n) (n-1)
  === A.get (merge xs ys n 0) (n-1)
  *** QED
    where
      zs  = merge xs ys (n-1) 0
      xs_n = A.get xs (n-1)


-- Commenting out intermediate steps greatly reduces the runtime (12'5 -> 3'53)
-- showing the output of merge is sorted if the inputs are sorted
-- TODO: Interesting observation: one less line of proof increase the compile time by 1/5 (from 100s to 80s)
{-@ lma_merge :: xs:{isSorted xs && A.size xs > 0} -> ys:{isSorted ys} -> n:{v:Nat | v <= A.size xs} -> m:{v:Nat | v <= A.size ys} 
      -> { isSortedFstN (merge xs ys n m) (n+m)} / [n+m]@-}
lma_merge :: Ord a => A.Array a -> A.Array a -> Int -> Int -> Proof
-- -- lma_merge [] ys _ _ = ()
lma_merge xs ys 0 0 = ()
lma_merge xs ys 0 1 = ()
lma_merge xs ys 1 0 = ()
lma_merge xs ys 0 m 
  = isSortedFstN mer1 m
  -- === (((A.get mer1 (m-2)) <= (A.get mer1 (m-1))) && (isSortedFstN mer1 (m-1)))
  -- === (((A.get mer2 (m-2)) <= (A.get mer2 (m-1))) && (isSortedFstN mer2 (m-1)))
    ? (A.lma_gs zs (m-1) ys_m) &&& (A.lma_gns zs (m-1) (m-2) ys_m)
  -- === (((A.get zs (m-2)) <= ys_m) && (isSortedFstN mer2 (m-1)))
    ? lma_isfn_set zs ys_m (m-1) (m-1)
  -- === (((A.get zs (m-2)) <= ys_m) && (isSortedFstN zs (m-1)))
    ? lma_merge xs ys 0 (m-1)
  -- === ((A.get zs (m-2)) <= ys_m)
    ? lma_merge_max_m xs ys (m-1) (ys_m ? lma_is_isfn ys m)
  === True
  *** QED
    where 
      mer1 = (merge xs ys 0 m)
      mer2 = (A.set zs (m-1) ys_m)
      zs =  merge xs ys 0 (m-1)
      ys_m = (A.get ys (m-1))
lma_merge xs ys n 0 
  = isSortedFstN mer1 n
  -- === (((A.get mer1 (m-2)) <= (A.get mer1 (m-1))) && (isSortedFstN mer1 (m-1)))
  -- === (((A.get mer2 (n-2)) <= (A.get mer2 (n-1))) && (isSortedFstN mer2 (n-1)))
    ? (A.lma_gs zs (n-1) xs_n) &&& (A.lma_gns zs (n-1) (n-2) xs_n)
  -- === (((A.get zs (n-2)) <= xs_n) && (isSortedFstN mer2 (n-1)))
    ? lma_isfn_set zs xs_n (n-1) (n-1)
  -- === (((A.get zs (n-2)) <= xs_n) && (isSortedFstN zs (n-1)))
    ? lma_merge xs ys (n-1) 0
  -- === ((A.get zs (n-2)) <= xs_n)
    ? lma_merge_max_n xs ys (n-1) (xs_n ? lma_is_isfn xs n)
  === True
  *** QED
    where 
      mer1 = (merge xs ys n 0)
      mer2 = (A.set zs (n-1) xs_n)
      zs =  merge xs ys (n-1) 0
      xs_n = (A.get xs (n-1))

lma_merge xs ys n m = 
  let 
    mer1 = (merge xs ys n m)
    mer2 = (A.set zs1 (m+n-1) ys_m)
    mer3 = (A.set zs2 (m+n-1) xs_n)
    zs1 = merge xs ys n (m-1)
    zs2 = merge xs ys (n-1) m
    xs_n = A.get xs (n-1)
    ys_m = A.get ys (m-1)
    merged = (A.set (merge xs ys (n) (m-1)) (m+n-1) ys_m) 
  in case xs_n <= ys_m of
    True -> isSortedFstN mer1 (n+m)
      -- === (((A.get mer1 (n+m-2)) <= (A.get mer1 (n+m-1))) && (isSortedFstN mer1 (n+m-1)))
      -- === (((A.get mer2 (n+m-2)) <= (A.get mer2 (n+m-1))) && (isSortedFstN mer2 (n+m-1)))
        ? (A.lma_gs zs1 (n+m-1) ys_m) &&& (A.lma_gns zs1 (n+m-1) (n+m-2) ys_m)
      -- === (((A.get zs1 (n+m-2)) <= ys_m) &&  (isSortedFstN mer2 (n+m-1)))
        ? lma_isfn_set zs1 ys_m (n+m-1) (n+m-1)
      -- === (((A.get zs1 (n+m-2)) <= ys_m) && (isSortedFstN zs1 (n+m-1)))
        ? lma_merge xs ys n (m-1)
      -- === ((A.get zs1 (n+m-2)) <= ys_m)-- ys_m => A.get (merge xs ys n (m-1)) (n+m-2)
        ? (if m > 1
            then lma_merge_max xs ys n (m-1) (ys_m ? (lma_is_isfn ys m))  
            else lma_merge_max_n xs ys n ys_m)
      === True
      *** QED
    False -> isSortedFstN mer1 (n+m) 
      -- === (((A.get mer1 (n+m-2)) <= (A.get mer1 (n+m-1))) && (isSortedFstN mer1 (n+m-1))) 
      -- === (((A.get mer3 (n+m-2)) <= (A.get mer3 (n+m-1))) && (isSortedFstN mer3 (n+m-1)))
      -- ==! True *** QED
        ? (A.lma_gs zs2 (n+m-1) xs_n) &&& (A.lma_gns zs2 (n+m-1) (n+m-2) xs_n)
      -- === (((A.get zs2 (n+m-2)) <= xs_n) && (isSortedFstN mer3 (n+m-1)))
        ? lma_isfn_set zs2 xs_n (n+m-1) (n+m-1)
      -- === (((A.get zs2 (n+m-2)) <= xs_n) && (isSortedFstN zs2 (n+m-1)))
        ? lma_merge xs ys (n-1) m
      -- === ((A.get zs2 (n+m-2)) <= xs_n) -- ys_m => A.get (merge xs ys n (m-1)) (n+m-2)
        ? (if n > 1
            then lma_merge_max xs ys (n-1) m (xs_n ? (lma_is_isfn xs n)) 
            else lma_merge_max_m xs ys m xs_n)
      === True
      *** QED
 

{-@ lma_msort :: xs:_
      -> { isSortedFstN (msort xs) (A.size xs)} / [A.size xs] @-}
lma_msort ::  Ord a => A.Array a -> Proof
lma_msort xs  
  | (A.size xs == 0) = ()
  | (A.size xs == 1) = ()
  | otherwise      =
    let 
      ls' = (msort ls)
      rs' = (msort rs)
      (ls, rs) = splitMid xs
      sxs = merge ls' rs' (A.size ls') (A.size rs')
      n = (A.size xs)
    in
      isSortedFstN (msort xs) n
      -- === isSortedFstN (merge ls' rs' (A.size ls') (A.size rs')) n
        ? (lma_merge (ls' ? (lma_msort ls)) (rs' ? (lma_msort rs)) (A.size ls') (A.size rs'))
      === True
      *** QED
