{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs         #-}
{-# LANGUAGE DeriveGeneric #-}

--module Array (Array(..), make, get, set, size, lma_gs, lma_gns, swap, lma_swap, lma_swap_eql) where
module Array where

import           GHC.Generics ( Generic )
import           Control.DeepSeq ( NFData(..) )
import           Language.Haskell.Liquid.ProofCombinators

{-@ data Array a = Arr {  lst   :: _
                        , left  :: {v: Nat | v <= (len lst) }
                        , right :: {v: Nat | v >= left && v <= (len lst)}
                        }
  @-}

data Array a = Arr { lst   :: [a]
                   , left  :: Int
                   , right :: Int}
               deriving Show

instance NFData a => NFData (Array a) where
  rnf (Arr ls l r) = rnf ls `seq` rnf l `seq` rnf r

-- The Token measure is intended to track when two Arrays have the same 
--   backing data structure. In the fake functional style, this is NOT
--   preserved under `set` operations
{-@ measure token :: [a] -> Nat @-}
{-@ predicate Token X  =  token (lst X) @-} 

-- basic API

{-@ reflect make @-}
{-@ make :: n:Nat -> x:_ -> xs:{(size xs) = n} @-}
make :: Int -> a -> Array a
make 0 x = Arr [] 0 0
make n x = let Arr lst l r = make (n-1) x in Arr (x:lst) l (r+1)

{-@ measure size @-}
{-@ size :: xs:_ -> Nat @-}
size :: Array a -> Int
size (Arr _ l r) = r-l

{-@ reflect listSize @-}
{-@ listSize :: xs:_ -> Nat @-}
listSize :: [a] -> Int
listSize []     = 0
listSize (_:xs) = 1 + (listSize xs)

{-@ reflect getList @-}
{-@ getList :: xs:_ -> {n:Nat | n < len xs } -> x:_ @-}
getList :: [a] -> Int -> a
--getList []    n = undefined
getList (x:_) 0 = x
getList (_:xs) n = getList xs (n-1)

--size2 :: Array a -> (Ur Int, Array a)
--size2 xs = (Ur (size xs), xs)

{-@ reflect get @-}
{-@ get :: xs:_ -> {n:Nat | n < size xs } -> x:_ @-}
get :: Array a -> Int -> a
get (Arr lst l r) n = getList lst (l+n)

{-@ reflect setList @-}  -- the assume needed to tell LH that it's the same array
{-@ setList :: xs:_ -> {n:Nat | n < len xs } -> x:_ 
                           -> { nxs:_ | (len nxs) == (len xs) } @-}
--                           -> { nxs:_ | (len nxs) == (len xs) && token xs == token nxs} @-}
setList :: [a] -> Int -> a -> [a]
--setList []     n _ = []                     -- needed if refinements aren't checked
setList (x:xs) 0 y = (y:xs)
setList (x:xs) n y = x:(setList xs (n-1) y)

{-@ reflect arrayWithProof @-}
arrayWithProof :: [a] -> Proof -> [a]
arrayWithProof a _ = a

--get2 :: Array a -> Int -> (Ur a, Array a)
--get2 xs i = (Ur (get xs i), xs)

{-@ reflect set @-}
{-@ set :: xs:_ -> {n:Nat | n < size xs } -> x:_ 
                -> nxs:{(size nxs) = (size xs) } @-}
--                -> nxs:{(size nxs) = (size xs) && Token xs == Token nxs } @-}
set :: Array a -> Int -> a -> Array a
set (Arr arr l r) n y = Arr (setList arr (l+n) y) l r --  `arrayWithProof` setListToken arr (l+n) y

{-@ reflect slice @-}
{-@ slice :: xs:_ -> {l:Nat | l <= size xs } -> {r:Nat | r <= size xs && l <= r} 
                  -> { ys:_ | size ys == r-l && Token xs == Token ys } @-}
--                  -> { ys:_ | size ys == r-l } @-}
slice :: Array a -> Int -> Int -> Array a
slice (Arr lst l r) l' r' = Arr lst (l+l') (l+r')

--append :: Array a -> Array a -> Array a
--append = (++)

fromList :: [a] -> Array a
fromList ls = Arr ls 0 (length ls)

--------------------------------------------------------------------------------
-- | Proofs
--------------------------------------------------------------------------------

-- lemma showing that get n from set n xs x is x
{-@ lma_gs_list :: xs:_ -> n:{v:Nat | v < len xs } -> x:_
      -> {getList (setList xs n x) n = x} @-}
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
      -> {get (set xs n x) n = x} @-}
lma_gs :: Array a -> Int -> a -> Proof
lma_gs (Arr lst l r) n x = lma_gs_list lst (l+n) x

-- lemma showing that get n from set m xs x is
{-@ lma_gns_list :: xs:_ -> n:{v:Nat | v < len xs } -> m:{v:Nat | v /= n && v < len xs} -> x:_
      -> {getList (setList xs n x) m = getList xs m} @-}
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

{-@ lma_gns :: xs:_ -> n:{v:Nat | v < size xs } -> m:{v:Nat | v /= n && v < size xs} -> x:_
      -> {get (set xs n x) m = get xs m} @-}
lma_gns :: Array a -> Int -> Int -> a -> Proof
lma_gns (Arr lst l r) n m x = lma_gns_list lst (l+n) (l+m) x

-- advanced operations

{-@ reflect swap @-}
{-@ swap :: xs:(Array a) -> { i:Int | 0 <= i && i < size xs } -> { j:Int | 0 <= j && j < size xs }
                         -> { ys:(Array a) | size xs == size ys } @-}
swap :: Array a -> Int -> Int -> Array a
swap xs i j = let xi  = get xs i
                  xs' = set xs i (get xs j)
               in set xs' j xi

{-@ lma_swap :: xs:(Array a) -> { i:Int | 0 <= i && i < size xs } -> { j:Int | 0 <= j && j < size xs }
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

{-@ lma_swap_eql :: xs:(Array a) -> { i:Int | 0 <= i && i < size xs } -> { j:Int | 0 <= j && j < size xs }
                                 -> { k:Int | 0 <= k && k < size xs && k /= i && k /= j }
                                 -> { pf:_  | get (swap xs i j) k == get xs k } @-}
lma_swap_eql :: Array a -> Int -> Int -> Int -> Proof
lma_swap_eql xs i j k = () ? lma_gns xs' j k xi
                           ? lma_gns xs  i k (get xs j)
  where
    xi   = get xs  i
    xs'  = set xs  i (get xs j)
