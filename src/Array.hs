{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs         #-}
{-# LANGUAGE DeriveGeneric #-}

module Array where
{-module Array
  (
    -- * Array type
    Array

    -- * Construction and querying
  , make, get, set, slice, size, append, swap

    -- * Linear versions
  , size2, get2

    -- * LiqidHaskell lemmas
  , lma_gs, lma_gns, lma_swap, lma_swap_eql
  ) where
-}

import           Prelude hiding (take, drop)
import           Control.DeepSeq ( NFData(..) )
import           System.IO.Unsafe
import           System.Random

import           Language.Haskell.Liquid.ProofCombinators

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
               deriving Show

-- newtype Ur a = Ur a

instance NFData a => NFData (Array a) where
  rnf (Arr ls l r t) = rnf ls `seq` rnf l `seq` rnf r `seq` rnf t

-- The token measure is intended to track when two Arrays have the same 
--   backing data structure. In the fake functional style, this is NOT
--   preserved under `set` operations
{-   @ measure token :: xs:Array a -> { v:Int | v == tok xs } @-}

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
               -> (Int, Array a)<{ \n zs -> n == size xs && 
                                                 xs == zs }> @-}
size2 :: Array a -> (Int, Array a)
size2 xs = (size xs, xs)                           -- (Ur (size xs), xs)

{-@ reflect listSize @-}
{-@ listSize :: xs:_ -> Nat @-}
listSize :: [a] -> Int
listSize []     = 0
listSize (_:xs) = 1 + (listSize xs)

--fromList :: [a] -> Array a
--fromList ls = Arr ls 0 (length ls)

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

{-@ reflect slice @-} -- need axiom for the token being the same 
{-@ slice :: xs:_ -> { l:Nat | l <= size xs } -> { r:Nat | l <= r && r <= size xs } 
                  -> { ys:_ | size ys == r-l         && token xs == token ys && 
                              left ys == left xs + l && right ys == left xs + r &&
                                                        right ys == right xs - size xs + r } @-}
slice :: Array a -> Int -> Int -> Array a
slice (Arr lst l r t) l' r' = Arr lst' (l+l') (l+r') t
  where
    lst' = take (r' - l') (drop l' lst)

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
{-@ reflect append @-}
{-@ append :: xs:Array a 
        -> { ys:Array a | token xs == token ys && right xs == left ys }
        -> { zs:Array a | token xs == token zs && size zs == size xs + size ys &&
                          left xs == left zs && right ys == right zs } @-}
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

{-@ lma_gs :: xs:_ -> n:{v:Nat | v < size xs } -> x:_
      -> {pf:_ | get (set xs n x) n = x} @-}
lma_gs :: Array a -> Int -> a -> Proof
lma_gs (Arr lst l r _) n x = lma_gs_list lst n x

{-@ lma_gs2 :: xs:_ -> n:{v:Nat | v < size xs } -> x:_
      -> {pf:_ | fst (get2 (set xs n x) n) = x} @-}
lma_gs2 :: Array a -> Int -> a -> Proof
lma_gs2 xs n x = lma_gs xs n x

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

{-@ lma_gns :: xs:_ -> n:{v:Nat | v < size xs } 
          -> m:{v:Nat | v /= n && v < size xs } -> x:_
          -> { pf:_ | get (set xs n x) m = get xs m} @-}
lma_gns :: Array a -> Int -> Int -> a -> Proof
lma_gns (Arr lst l r _) n m x = lma_gns_list lst n m x

{-@ lma_gns2 :: xs:_ -> n:{v:Nat | v < size xs } 
          -> m:{v:Nat | v /= n && v < size xs } -> x:_
          -> { pf:_ | fst (get2 (set xs n x) m) == fst (get2 xs m) } @-}
lma_gns2 :: Array a -> Int -> Int -> a -> Proof
--lma_gns2 (Arr lst _ _ _) n m x = lma_gns_list lst n m x
lma_gns2 xs n m x = lma_gns xs n m x

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
