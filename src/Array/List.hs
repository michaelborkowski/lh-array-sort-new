{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{- @ LIQUID "--no-environment-reduction"      @-}
{-@ LIQUID "--prune-unsorted" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE CPP           #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE DeriveGeneric #-}

module Array.List {-
  (
    -- * Array type
    Array

    -- * Construction and querying
  , make, get, set, slice, size, append, swap

    -- * Linear versions
  , size2, get2

    -- * Convert to/from lists
  , fromList, toList

    -- * LiqidHaskell lemmas
  , lma_gs_list, lma_gns_list
  ) -} where


import           Prelude hiding (take, drop)
import           Control.DeepSeq ( NFData(..) )
import           System.IO.Unsafe
import           System.Random

import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators

--------------------------------------------------------------------------------

{-@ data Array a = Arr {  lst   :: [a]
                       ,  left  :: Nat
                       ,  right :: { v: Nat | v >= left && v - left == len lst }
                       ,  tok   :: Int
                       }
  @-}

data Array a = Arr {  lst   :: [a]  -- lst only contains from left ... right-1
                   ,  left  :: Int
                   ,  right :: Int
                   ,  tok   :: Int }
               deriving (Eq, Show)

-- newtype Ur a = Ur a

instance NFData a => NFData (Array a) where
  rnf (Arr ls l r t) = rnf ls `seq` rnf l `seq` rnf r `seq` rnf t

-- The token measure is intended to track when two Arrays have the same
--   backing data structure. In the fake functional style, this is NOT
--   preserved under `set` operations
{-     @ measure token :: xs:Array a -> { v:Nat | v == tok xs } @-}

{-@ reflect token @-}
{-@ token :: xs:Array a -> { v:Int | v == tok xs } @-}
token :: Array a -> Int
token xs = tok xs

-- | basic API

  -- make and size

{- @ reflect make' @-}
{-@ make' :: n:Nat -> x:_ -> xs:{(size xs) = n && left xs == 0 && right xs == n} @-}
make' :: Int -> a -> Array a
make' 0 x = Arr [] 0 0 0
make' n x = let Arr lst l r _ = make' (n-1) x in Arr (x:lst) l (r+1) 0

{-@ make :: n:Nat -> x:_ -> xs:{(size xs) = n && left xs == 0 && right xs == n} @-}
make :: Int -> a -> Array a
make n x = Arr lst l r t
  where
    Arr lst l r _ = make' n x
    t             = unsafePerformIO (randomIO :: IO Int)

{-@ measure size @-}
{-@ size :: xs:_ -> Nat @-}
size :: Array a -> Int
size (Arr _ l r _) = r-l

{-@ reflect size2 @-}
{-@ size2 :: xs:(Array a)
               -> (Int, Array a)<{
                      \n zs -> n == size xs && xs == zs }> @-}
size2 :: Array a -> (Int, Array a)
size2 xs = (size xs, xs)                           -- (Ur (size xs), xs)

{-@ reflect listSize @-}
{-@ listSize :: xs:_ -> Nat @-}
listSize :: [a] -> Int
listSize []     = 0
listSize (_:xs) = 1 + (listSize xs)

fromList :: [a] -> Array a
fromList ls = Arr ls 0 (length ls) t
  where
    t = unsafePerformIO (randomIO :: IO Int)

{-@ reflect toList @-}
{-@ toList :: xs:_ -> { xls:[a] | xls == lst xs && len xls == size xs } @-}
toList :: Array a -> [a]
toList (Arr ls _ _ _) = ls

  -- get

{-@ reflect getList @-}
{-@ getList :: xs:_ -> {n:Nat | n < len xs } -> x:_ @-}
getList :: [a] -> Int -> a
getList (x:_)  0 = x
getList (_:xs) n = getList xs (n-1)

{-@ reflect get @-}
{-@ get :: xs:_ -> {n:Nat | n < size xs } -> x:_ @-}
get :: Array a -> Int -> a
get (Arr lst _ _ _) n = getList lst n

{-@ reflect get2 @-}
{-@ get2 :: xs:Array a -> {n:Nat | n < size xs }
              -> (a, Array a)<{\ x zs -> x == get xs n && xs == zs }> @-}
get2 :: Array a -> Int -> (a, Array a)
get2 xs i = (get xs i, xs)                  -- (Ur (get xs i), xs)

  -- set

{-@ reflect setList @-}
{-@ setList :: xs:_ -> {n:Nat | n < len xs } -> x:_
                    -> { nxs:_ | (len nxs) == (len xs) } @-}
setList :: [a] -> Int -> a -> [a]
setList (x:xs) 0 y = (y:xs)
setList (x:xs) n y = x:(setList xs (n-1) y)

{-@ reflect set @-}
{-@ set :: xs:_ -> { n:Nat | n < size xs } -> x:_
                -> { nxs:(Array a) | left xs == left nxs && right xs == right nxs &&
                                     token xs == token nxs && size xs == size nxs } @-}
set :: Array a -> Int -> a -> Array a
set (Arr arr l r t) n y = Arr (setList arr n y) l r t

  -- slices, splits, and appends

{-@ reflect copy @-}
{-@ copy :: xs:_ -> { xi:Nat | xi <= size xs } -> ys:_
                 -> { yi:Nat | yi <= size ys } 
                 -> { n:Nat  | xi + n <= size xs && yi + n <= size ys }
                 -> { zs:_   | size ys == size zs && token ys == token zs &&
                               left ys == left zs && right ys == right zs } / [n] @-}
copy :: Array a -> Int -> Array a -> Int -> Int -> Array a
copy xs xi ys yi 0 = ys
copy xs xi ys yi n = set (copy xs xi ys yi (n-1)) (yi + n - 1) (get xs (xi + n - 1))
--            *or*   copy xs xi (set ys (yi + n - 1) (get xs (xi + n - 1))) yi (n-1)
-- alternative would be
-- copy xs xi ys yi 0 = ys
-- copy xs xi ys yi n | xi == size xs  = ys
--                    | otherwise      = set (copy xs (xi+1) ys (yi+1) (n-1)) yi (get xs xi)
--            *or*                       copy xs (xi+1) (set ys yi (get xs xi)) (yi+1) (n-1)

{-@ reflect copy2 @-}
{-@ copy2 :: xs:_ -> { xi:Nat | xi <= size xs } -> ys:_
                  -> { yi:Nat | yi <= size ys }
                  -> { n:Nat  | xi + n <= size xs && yi + n <= size ys }
                  -> { zs:_   | xs == fst zs && snd zs == copy xs xi ys yi n &&
                                size (snd zs) == size ys && token (snd zs) == token ys &&
                                left (snd zs) == left ys && right (snd zs) == right ys } @-}
copy2 :: Array a -> Int -> Array a -> Int -> Int -> (Array a, Array a)
copy2 xs xi ys yi n = (xs, copy xs xi ys yi n)

{-@ reflect slice @-} -- need axiom for the token being the same
{-@ slice :: xs:_ -> { l:Nat | l <= size xs } -> { r:Nat | l <= r && r <= size xs }
                  -> { ys:_ | size ys == r-l         && token xs == token ys &&
                              left ys == left xs + l && right ys == left xs + r &&
                                                        right ys == right xs - size xs + r && 
                              toList ys == take (r - l) (drop l (toList xs)) } @-}
slice :: Array a -> Int -> Int -> Array a
slice (Arr lst l r t) l' r' = Arr lst' (l+l') (l+r') t
  where
    lst' = take (r' - l') (drop l' lst)

{-@ reflect slice2 @-}
{-@ slice2 :: xs:_ -> { l:Nat | l <= size xs } -> { r:Nat | l <= r && r <= size xs } 
                  -> (Array a, Array a)<{\ ys zs -> xs == zs && ys = slice xs l r &&
                                                    left ys == left xs + l && right ys == left xs + r &&
                                                    right ys == right xs - size xs + r }> @-}
slice2 :: Array a -> Int -> Int -> (Array a, Array a)
slice2 xs l r = (slice xs l r, xs)

{-@ reflect conc @-}
{-@ conc :: xs:_ -> ys:_ -> { zs:_ | len zs == len xs + len ys } @-}
conc :: [a] -> [a] -> [a]
conc []     ys = ys
conc (x:xs) ys = x:(conc xs ys)

{-@ reflect take @-}
{-@ take :: n:Nat -> { xs:_ | n <= len xs } -> { zs:_ | len zs == n } @-}
take :: Int -> [a] -> [a]
take 0 _      = []
take n (x:xs) = x:(take (n-1) xs)

{-@ reflect drop @-}
{-@ drop :: n:Nat -> { xs:_ | n <= len xs } -> { zs:_ | len zs == len xs - n } @-}
drop :: Int -> [a] -> [a]
drop 0 xs     = xs
drop n (x:xs) = drop (n-1) xs

-- PRE-CONDITION: the two slices are backed by the same array.
-- removed for the parallel merge: 
{-@ reflect append @-}
{-@ append :: xs:Array a
        -> { ys:Array a | token xs == token ys && right xs == left ys }
        -> { zs:Array a | token xs == token zs && size zs == size xs + size ys &&
                          left xs == left zs && right ys == right zs &&
                          toList zs == conc (toList xs) (toList ys) } @-}
append :: Array a -> Array a -> Array a
append (Arr arr1 l1 _r1 t) (Arr arr2 _l2 r2 _t) = Arr (conc arr1 arr2) l1 r2 t


--------------------------------------------------------------------------------
-- | Proofs
--------------------------------------------------------------------------------

-- lemma showing that get n from set n xs x is x
{-@ lma_gs_list :: xs:_ -> n:{v:Nat | v < len xs } -> x:_
      -> {pf:_ | getList (setList xs n x) n = x} @-}
lma_gs_list :: [a] -> Int -> a -> Proof
lma_gs_list (x:xs) 0 x'
  = getList (setList (x:xs) 0 x') 0
  -- === getList (x':xs) 0
  === x'
  *** QED
lma_gs_list (x:xs) n x'
  =  getList (setList (x:xs) n x') n
  -- === getList (x:(setList xs (n-1) x')) n
  -- === getList (setList xs (n-1) x') (n-1)
    ? lma_gs_list xs (n-1) x'
  === x'
  *** QED



-- lemma showing that get n from set m xs x is
{-@ lma_gns_list :: xs:_ -> n:{v:Nat | v < len xs } -> m:{v:Nat | v /= n && v < len xs} -> x:_
      -> {pf:_ | getList (setList xs n x) m = getList xs m} @-}
lma_gns_list :: [a] -> Int -> Int -> a -> Proof
lma_gns_list (x:xs) 0 m x'
  = getList (setList (x:xs) 0 x') m
  -- === getList (x':xs) m
  -- === getList xs (m-1)
  === getList (x:xs) m
  *** QED

lma_gns_list (x:xs) n 0 x'
  = getList (setList (x:xs) n x') 0
  -- === getList (x:(setList xs (n-1) x')) 0
  -- === x
  === getList (x:xs) 0
  *** QED

lma_gns_list (x:xs) n m x'
  = getList (setList (x:xs) n x') m
  -- === getList (x:(setList xs (n-1) x')) m
  -- === getList (setList xs (n-1) x') (m-1)
    ? lma_gns_list xs (n-1) (m-1) x'
  -- === getList xs (m-1)
  === getList (x:xs) m
  *** QED


{-@ lem_getList_drop :: xs:_ -> { n:Nat | n < len xs } -> { i:Nat | n <= i && i < len xs }
                             -> { pf:_ | getList (drop n xs) (i-n) == getList xs i } @-}
lem_getList_drop :: [a] -> Int -> Int -> Proof
lem_getList_drop (x:xs) n i | n == 0    = ()
                            | otherwise = () ? lem_getList_drop xs (n-1) (i-1)

{-@ lem_getList_take :: xs:_ -> { n:Nat | 0 < n && n <= len xs } -> { i:Nat | i < n }
                             -> { pf:_ | getList (take n xs) i == getList xs i } @-}
lem_getList_take :: [a] -> Int -> Int -> Proof
lem_getList_take (x:xs) n i | i == 0    = ()
                            | otherwise = () ? lem_getList_take xs (n-1) (i-1)

{-@ lem_take_all :: xs:_ -> { pf:_ | take (len xs) xs == xs } @-}
lem_take_all :: [a] -> Proof
lem_take_all []     = ()
lem_take_all (x:xs) = () ? lem_take_all xs

{-@ lem_take_conc :: xs:_ -> ys:_ -> { pf:_ | take (len xs) (conc xs ys) == xs } @-}
lem_take_conc :: [a] -> [a] -> Proof
lem_take_conc []     ys = ()
lem_take_conc (x:xs) ys = () ? lem_take_conc xs ys

{-@ lem_drop_conc :: xs:_ -> ys:_ -> { pf:_ | drop (len xs) (conc xs ys) == ys } @-}
lem_drop_conc :: [a] -> [a] -> Proof
lem_drop_conc []     ys = ()
lem_drop_conc (x:xs) ys = () ? lem_drop_conc xs ys

{-@ lem_slice_append :: xs:_ -> { ys:_ | token xs == token ys && right xs == left ys }
                             -> { pf:_ | slice (append xs ys) 0 (size xs) == xs &&
                                         slice (append xs ys) (size xs) (size xs + size ys) == ys } @-}
lem_slice_append :: Array a -> Array a -> Proof
lem_slice_append (Arr xls _ _ _) (Arr yls _ _ _)  = () ? lem_take_conc xls yls 
                                                       ? lem_drop_conc xls yls
                                                       ? lem_take_all      yls
