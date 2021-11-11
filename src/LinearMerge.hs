{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}
-- {-@ LIQUID "--checks=lma_merge_max" @-}


-- {-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs #-}

module LinearMerge where

import           Prelude 
import           Language.Haskell.Liquid.ProofCombinators
-- import qualified Data.Set as S
import           Array as A
-- import           Equivalence
-- import           Language.Haskell.Liquid.Bag as B
-- 6'34 compiling time

--------------------------------------------------------------------------------
-- | Implementations
--------------------------------------------------------------------------------
 
-- >>>  merge [1:3:4:6] [2:5] 4 2
--

-- merging the first n,m indices of xs, ys
{-@ reflect merge @-}
{-@ merge :: xs:_ -> ys:_ -> zs:{(size zs) = ((size xs) + (size ys))} -> n:{v:Nat | v <= size xs} -> m:{v:Nat | v <= size ys} 
      -> ws:{(size ws) = (size zs)} / [m+n] @-}
merge :: Ord a => Array a -> Array a -> Array a -> Int -> Int -> Array a
merge xs ys zs 0 0 = zs
merge xs ys zs 0 m = let zs' = merge xs ys zs 0 (m-1) in (set zs' (m-1) (A.get ys (m-1)))
merge xs ys zs n 0 = let zs' = merge xs ys zs (n-1) 0 in (set zs' (n-1) (A.get xs (n-1)))
merge xs ys zs n m | xs_n <= ys_m = let zs' = merge xs ys zs (n) (m-1)   
                                    in (set zs' (m+n-1) ys_m)
                                    -- let zs' = set zs (m+n-1) ys_m 
                                    -- in merge xs ys zs' n (m-1)

                   | otherwise    = let zs' = merge xs ys zs (n-1) (m) 
                                  in (set zs' (m+n-1) xs_n)
                      where 
                        xs_n = A.get xs (n-1)
                        ys_m = A.get ys (m-1) 


-- >>>  msort (fromList [1,3,2,9,6,0,5,2,10,-1])
-- [-1,0,1,2,2,3,5,6,9,10]
-- TODO: Inefficient implementation 
-- need to show xs == ys 
{-@ reflect msort @-}
{-@ msort :: xs:_ -> ys:_ -> zs:{(size ys == size xs)} / [size xs] @-}
msort :: Ord a => Array a -> Array a -> Array a
msort xs ys | (size xs) == 0 = ys
            | (size xs) == 1 = ys
            | otherwise      = let  
                                  yls' = (msort xls yls)
                                  yrs' = (msort xrs yrs)
                                  (xls, xrs) = splitMid xs
                                  (yls, yrs) = splitMid ys
                                in merge yls' yrs' xs (size yls') (size yrs')


{-@ reflect splitMid @-}
{-@ splitMid :: xs:{size xs >= 2} -> {t:_ | ((size (fst t)) < (size xs) && (size (snd t)) < (size xs)) && (size xs = (size (fst t)) + (size (snd t)))} @-}
splitMid :: Array a -> (Array a, Array a)
splitMid xs = ((subArray xs 0 m), (subArray xs m n)) -- TODO: Modify this as well
  where 
    n = size xs 
    m = mydiv n



-- mydiv n = div n 2
{-@ reflect mydiv @-}
{-@ mydiv :: n:{n >= 2} -> m:{v:Nat | (v > 0 && v < n)} @-}
mydiv :: Int -> Int
mydiv 2 = 1
mydiv 3 = 1 
mydiv n = 1 + (mydiv (n-2))

{-@ reflect subArrayR @-}
{-@ subArrayR :: xs:{size xs >= 1} -> n:{v:Nat | v <= size xs} -> m:{v:Nat | n <= m && m <= size xs} -> c:{v:Nat | v <= m-n} -> ys:{size ys == m-n} / [c]@-}
subArrayR :: Array a -> Int -> Int -> Int -> Array a
subArrayR xs n m 0 = make (m-n) (A.get xs 0)  
subArrayR xs n m c = set (subArrayR xs n m (c-1)) (c-1) (A.get xs (n+c-1))

{-@ reflect subArray @-}
{-@ subArray :: xs:{size xs >= 1} -> n:{v:Nat | v <= size xs} -> m:{v:Nat | n <= m && m <= size xs} -> ys:{size ys == m-n}@-}
subArray :: Array a -> Int -> Int -> Array a
subArray xs n m = subArrayR xs n m (m-n)

--------------------------------------------------------------------------------
-- | Proofs
--------------------------------------------------------------------------------
{-

-- TODO: I really want to A.get rid of the edge cases where n-1 can be -1
-- FIXME: constrains z >= (A.get xs (n-1)) does not enforce n > 0, but it makes the program into a loop
--        nor does it check the constrain of n when i am calling this method, another loop
-- n = 0 implies  -- TODO: Forever loop, Not working
-- {-@ lma_merge_max :: xs:{isSorted xs} -> ys:{isSorted ys} -> n:{v:Nat | v <= size xs} -> m:{v:Nat | v > 0 && v <= size ys} -> z:{  ((n > 0) => (z >= (A.get xs (n-1)))) && z >= (A.get ys (m-1))}
      -- -> { z >= A.get (merge xs ys n m) (n+m-1) } @-}
{-@ lma_merge_max :: xs:{isSorted xs} -> ys:{isSorted ys} -> n:{v:Nat | v > 0 && v <= size xs} -> m:{v:Nat | v > 0 && v <= size ys} -> z:{  z >= (A.get xs (n-1)) && z >= (A.get ys (m-1))} 
      -> { z >= A.get (merge xs ys n m) (n+m-1) } @-}
lma_merge_max ::  Ord a => Array a -> Array a -> Int -> Int -> a -> Proof
-- lma_merge_max xs ys 0 m z 
--   = z
--   =>= ys_m
--     ? lma_gs zs (m-1) ys_m
--   === A.get (set zs (m-1) ys_m) (m-1)
--   === A.get (merge xs ys 0 m) (m-1)
--   *** QED
--     where 
--       zs  = merge xs ys 0 (m-1)
--       ys_m = A.get ys (m-1)
lma_merge_max xs ys n m z 
  | xs_n <= ys_m 
    = z
    =>= ys_m
      ? lma_gs zs (m+n-1) ys_m
    -- === A.get (set zs (m+n-1) ys_m) (m+n-1)
    === A.get (merge xs ys n m) (m+n-1)
    *** QED
  | otherwise
    = z
    =>= xs_n
      ? lma_gs zs' (m+n-1) xs_n
    -- === A.get (set zs' (m+n-1) xs_n) (m+n-1)
    === A.get (merge xs ys n m) (m+n-1)
    *** QED
      where 
        zs  = merge xs ys n (m-1)
        zs' = merge xs ys (n-1) m
        xs_n = A.get xs (n-1)
        ys_m = A.get ys (m-1)

-- TODO: Dumb to write this proof separately, for the case n = 0
{-@ lma_merge_max_m :: xs:_ -> ys:{isSorted ys} -> m:{v:Nat | v > 0 && v <= size ys} -> z:{ z >= (A.get ys (m-1))}
      -> { z >= A.get (merge xs ys 0 m) (m-1) } @-}
lma_merge_max_m ::  Ord a => Array a -> Array a -> Int -> a -> Proof
lma_merge_max_m xs ys m z 
  = z
  =>= ys_m
    ? lma_gs zs (m-1) ys_m
  -- === A.get (set zs (m-1) ys_m) (m-1)
  === A.get (merge xs ys 0 m) (m-1)
  *** QED
    where
      zs  = merge xs ys 0 (m-1)
      ys_m = A.get ys (m-1)

-- TODO: Dumb to write this proof separately, for the case n = 0
{-@ lma_merge_max_n :: xs:{isSorted xs} -> ys:_ -> n:{v:Nat | v > 0 && v <= size xs} -> z:{ z >= (A.get xs (n-1))}
      -> { z >= A.get (merge xs ys n 0) (n-1) } @-}
lma_merge_max_n ::  Ord a => Array a -> Array a -> Int -> a -> Proof
lma_merge_max_n xs ys n z 
  = z
  =>= xs_n
    ? lma_gs zs (n-1) xs_n
  -- === A.get (set zs (n-1) xs_n) (n-1)
  === A.get (merge xs ys n 0) (n-1)
  *** QED
    where
      zs  = merge xs ys (n-1) 0
      xs_n = A.get xs (n-1)


-- Commenting out intermediate steps greatly reduces the runtime (12'5 -> 3'53)
-- showing the output of merge is sorted if the inputs are sorted
-- TODO: Interesting observation: one less line of proof increase the compile time by 1/5 (from 100s to 80s)
{-@ lma_merge :: xs:{isSorted xs} -> ys:{isSorted ys} -> n:{v:Nat | v <= size xs} -> m:{v:Nat | v <= size ys} 
      -> { isSortedFstN (merge xs ys n m) (n+m)} / [n+m]@-}
lma_merge :: Ord a => Array a -> Array a -> Int -> Int -> Proof
-- -- lma_merge [] ys _ _ = ()
lma_merge xs ys 0 0 = ()
lma_merge xs ys 0 1 = ()
lma_merge xs ys 1 0 = ()
lma_merge xs ys 0 m 
  = isSortedFstN mer1 m
  -- === (((A.get mer1 (m-2)) <= (A.get mer1 (m-1))) && (isSortedFstN mer1 (m-1)))
  -- === (((A.get mer2 (m-2)) <= (A.get mer2 (m-1))) && (isSortedFstN mer2 (m-1)))
    ? (lma_gs zs (m-1) ys_m) &&& (lma_gns zs (m-1) (m-2) ys_m)
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
      mer2 = (set zs (m-1) ys_m)
      zs =  merge xs ys 0 (m-1)
      ys_m = (A.get ys (m-1))
lma_merge xs ys n 0 
  = isSortedFstN mer1 n
  -- === (((A.get mer1 (m-2)) <= (A.get mer1 (m-1))) && (isSortedFstN mer1 (m-1)))
  -- === (((A.get mer2 (n-2)) <= (A.get mer2 (n-1))) && (isSortedFstN mer2 (n-1)))
    ? (lma_gs zs (n-1) xs_n) &&& (lma_gns zs (n-1) (n-2) xs_n)
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
      mer2 = (set zs (n-1) xs_n)
      zs =  merge xs ys (n-1) 0
      xs_n = (A.get xs (n-1))

lma_merge xs ys n m = 
  let 
    mer1 = (merge xs ys n m)
    mer2 = (set zs1 (m+n-1) ys_m)
    mer3 = (set zs2 (m+n-1) xs_n)
    zs1 = merge xs ys n (m-1)
    zs2 = merge xs ys (n-1) m
    xs_n = A.get xs (n-1)
    ys_m = A.get ys (m-1)
    merged = (set (merge xs ys (n) (m-1)) (m+n-1) ys_m) 
  in case xs_n <= ys_m of
    True -> isSortedFstN mer1 (n+m)
      -- === (((A.get mer1 (n+m-2)) <= (A.get mer1 (n+m-1))) && (isSortedFstN mer1 (n+m-1)))
      -- === (((A.get mer2 (n+m-2)) <= (A.get mer2 (n+m-1))) && (isSortedFstN mer2 (n+m-1)))
        ? (lma_gs zs1 (n+m-1) ys_m) &&& (lma_gns zs1 (n+m-1) (n+m-2) ys_m)
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
        ? (lma_gs zs2 (n+m-1) xs_n) &&& (lma_gns zs2 (n+m-1) (n+m-2) xs_n)
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
      -> { isSortedFstN (msort xs) (size xs)} / [size xs] @-}
lma_msort ::  Ord a => Array a -> Proof
lma_msort xs  
  | (size xs == 0) = ()
  | (size xs == 1) = ()
  | otherwise      =
    let 
      ls' = (msort ls)
      rs' = (msort rs)
      (ls, rs) = splitMid xs
      sxs = merge ls' rs' (size ls') (size rs')
      n = (size xs)
    in
      isSortedFstN (msort xs) n
      -- === isSortedFstN (merge ls' rs' (size ls') (size rs')) n
        ? (lma_merge (ls' ? (lma_msort ls)) (rs' ? (lma_msort rs)) (size ls') (size rs'))
      === True
      *** QED



----

topLevel xs = msort xs tmp 
  where 
    tmp = make (size xs) (A.get xs 0)
    
msort' :: Ord a => Array a -> Array a -> Array a
msort' xs zs  
  | (size xs) == 0 = zs
  | (size xs) == 1 = zs
  | otherwise      = let zls' = msort' xls zls
                         zrs' = msort' xrs zrs
                         (xls, xrs) = splitMid xs
                         (zls, zrs) = splitMid zs
                     in merge' zls' zrs' xs (size zls') (size zrs')

-- merging the first n,m indices of xs, ys
{- reflect merge' @-}
{- merge' :: xs:_ -> ys:_ -> n:{v:Nat | v <= size xs} -> m:{v:Nat | v <= size ys} 
      -> zs:{(size zs) = ((size xs) + (size ys))} / [m+n] @-}
merge' :: Ord a => Array a -> Array a -> Array a -> Int -> Int -> Array a
-- merge' [] ys _ _ = ys
merge' xs ys zs 0 0 = zs -- (make ((size xs)+(size ys)) (A.get xs 0))
merge' xs ys zs 0 m = let zs' = merge' xs ys zs 0 (m-1) in (set zs' (m-1) (A.get ys (m-1)))
merge' xs ys zs n 0 = let zs' = merge' xs ys zs (n-1) 0 in (set zs' (n-1) (A.get xs (n-1)))
merge' xs ys zs n m | xs_n <= ys_m = let zs' = merge' xs ys zs (n) (m-1)   
                                  in (set zs' (m+n-1) ys_m)
                | otherwise    = let zs' = merge' xs ys zs (n-1) (m) 
                                  in (set zs' (m+n-1) xs_n)
                  where 
                    xs_n = A.get xs (n-1)
                    ys_m = A.get ys (m-1) 
-}