{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ infixr ++  @-}  -- TODO: Silly to have to rewrite this annotation!

{-# LANGUAGE GADTs         #-}
{-# LANGUAGE DeriveGeneric #-}

--module Array (Array(..), make, get, set, size, lma_gs, lma_gns, swap, lma_swap, lma_swap_eql) where
module Array where

import           Prelude hiding (take, drop)
import           GHC.Generics ( Generic )
import           Control.DeepSeq ( NFData(..) )
import           Language.Haskell.Liquid.ProofCombinators


{-@ data Array a = Arr {  lst   :: [a]
                       ,  left  :: {v: Nat | v <= (len lst) }
                       ,  right :: {v: Nat | v >= left && v <= (len lst)}
                       }
  @-}

data Array a = Arr {  lst   :: [a]
                   ,  left  :: Int
                   ,  right :: Int }
               deriving Show

newtype Ur a = Ur a

instance NFData a => NFData (Array a) where
  rnf (Arr ls l r) = rnf ls `seq` rnf l `seq` rnf r

-- The token measure is intended to track when two Arrays have the same 
--   backing data structure. In the fake functional style, this is NOT
--   preserved under `set` operations
{-@ measure token :: Array a -> Nat @-}

-- | basic API

  -- make and size

{-@ reflect make @-}
{-@ make :: n:Nat -> x:_ -> xs:{(size xs) = n} @-}
make :: Int -> a -> Array a
make 0 x = Arr [] 0 0
make n x = let Arr lst l r = make (n-1) x in Arr (x:lst) l (r+1)

{-@ measure size @-}
{-@ size :: xs:_ -> Nat @-}
size :: Array a -> Int
size (Arr _ l r) = r-l

{-@ reflect size2 @-}
{-@ size2 :: xs:(Array a)
               -> (Ur Int, Array a)<{
                      \n zs -> n == size xs &&
                               left xs == left zs && right xs == right zs &&
                               size xs == size zs && token xs == token zs }> @-}
size2 :: Array a -> (Ur Int, Array a)
size2 xs = (Ur (size xs), xs)

{-@ reflect listSize @-}
{-@ listSize :: xs:_ -> Nat @-}
listSize :: [a] -> Int
listSize []     = 0
listSize (_:xs) = 1 + (listSize xs)

fromList :: [a] -> Array a
fromList ls = Arr ls 0 (length ls)

  -- get 

{-@ reflect getList @-}
{-@ getList :: xs:_ -> {n:Nat | n < len xs } -> x:_ @-}
getList :: [a] -> Int -> a
getList (x:_) 0 = x
getList (_:xs) n = getList xs (n-1)

{-@ reflect get @-}
{-@ get :: xs:_ -> {n:Nat | n < size xs } -> x:_ @-}
get :: Array a -> Int -> a
get (Arr lst l r) n = getList lst (l+n)

{-@ get2 :: xs:Array a -> {n:Nat | n < size xs }
              -> (Ur a, Array a)<{\ x zs -> size xs == size zs &&
                                            left xs == left zs && right xs == right zs &&
                                            token xs == token zs }> @-}
get2 :: Array a -> Int -> (Ur a, Array a)
get2 xs i = (Ur (get xs i), xs)

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
                                     (size nxs) = (size xs) } @-}
set :: Array a -> Int -> a -> Array a
set (Arr arr l r) n y = Arr (setList arr (l+n) y) l r 

{-@ assume axm_set_token :: xs:_ -> { n:Nat | n < size xs } -> x:_
                                 -> { pf:_  | token xs == token (set xs n x) } @-}
axm_set_token :: Array a -> Int -> a -> Proof
axm_set_token xs n x = ()

{-@ reflect withAxiom @-}
withAxiom :: Array a -> Proof -> Array a
withAxiom a _ = a

  -- slices, splits, and appends

{- @ reflect slice @-} -- need axiom for the token being the same 
{-@ slice :: xs:_ -> { l:Nat | l <= size xs } -> { r:Nat | l <= r && r <= size xs } 
                  -> { ys:_ | size ys == r-l &&
                              left ys == left xs + l && right ys == left xs + r } @-}
slice :: Array a -> Int -> Int -> Array a
slice (Arr lst l r) l' r' = Arr lst l' r'  
--  where
--    lst' = take (r' - l') (drop l' lst)



-- PRE-CONDITION: the two slices are backed by the same array.
{-@ reflect append @-}
{-@ append :: xs:Array a
        -> { ys:Array a | token xs == token ys && right xs == left ys }
        -> { zs:Array a | token xs == token zs &&
                          size zs == size xs + size ys &&
                          left xs == left zs && right ys == right zs } @-}
append :: Array a -> Array a -> Array a
append (Arr arr1 l1 _r1) (Arr arr2 _l2 r2) = undefined -- Arr (conc arr1 arr2) l1 r2


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

{-@ lma_gs :: xs:_ -> n:{v:Nat | v >= left xs && v < right xs } -> x:_
      -> {pf:_ | get (set xs n x) n = x} @-}
lma_gs :: Array a -> Int -> a -> Proof
lma_gs (Arr lst l r) n x = lma_gs_list lst (n-l) x

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

{-@ lma_gns :: xs:_ -> n:{v:Nat | v >= left xs && v < right xs } 
          -> m:{v:Nat | v /= n && v >= left xs && v < right xs } -> x:_
          -> { pf:_ | get (set xs n x) m = get xs m} @-}
lma_gns :: Array a -> Int -> Int -> a -> Proof
lma_gns (Arr lst l r) n m x = lma_gns_list lst (n-l) (m-l) x

{-
 -
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

-}
