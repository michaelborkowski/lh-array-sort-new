
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorder" @-}
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
import           Linear.Common
import qualified Linear.Unsafe  as Unsafe

import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import qualified Data.Primitive.Types as P

--------------------------------------------------------------------------------

-- nice trick from: https://github.com/leftaroundabout/trivial-constraint
class Unconstrained t
instance Unconstrained t

type HasPrim a =
#ifdef PRIM_MUTABLE_ARRAYS
  (P.Prim a)
#else
  Unconstrained a
#endif

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

{-@ reflect make' @-}
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

{-  @ reflect size2 @-}
{-@ size2 :: xs:(Array a)
               -> { tup:_ | unur (fst tup) == size xs && snd tup == xs } @-}
size2 :: Array a -. (Ur Int, Array a)
size2 xs = Unsafe.toLinear go (xs ? toProof (Unsafe.toLinear go xs === go xs))
  where
    {-@ go :: xs:(Array a)
               -> { tup:_ | unur (fst tup) == size xs && snd tup == xs } @-}
    go ys = (Ur (size ys), ys)

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
{-@ get2 :: n:Nat -> {xs:Array a | n < size xs }
              -> (Ur a, Array a)<{\ x zs -> unur x == get xs n && xs == zs }> @-}
get2 :: Int -> (Array a -. (Ur a, Array a))
get2 i = Unsafe.toLinear (\xs -> let xs' = get xs i
                                  in (Ur xs', xs))

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

{-@ reflect setLin @-}
{-@ setLin :: n:Nat -> x:_ -> { xs:_ | n < size xs }
                -> { nxs:(Array a) | left xs == left nxs && right xs == right nxs &&
                                     token xs == token nxs && size xs == size nxs &&
                                     nxs == set xs n x } @-}
setLin :: Int -> a -> (Array a -. Array a)
setLin n y = Unsafe.toLinear (\(Arr arr l r t) -> Arr (setList arr n y) l r t)

  -- copies

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
{-@ copy2 :: xi:Nat -> yi:Nat -> n:Nat
                  -> { xs:_ | xi <= size xs } -> { ys:_ | yi <= size ys && xi + n <= size xs && yi + n <= size ys }
                  -> { zs:_   | xs == fst zs && snd zs == copy xs xi ys yi n &&
                                size (snd zs) == size ys && token (snd zs) == token ys &&
                                left (snd zs) == left ys && right (snd zs) == right ys } @-}
copy2 :: Int -> Int -> Int -> (Array a -. (Array a -. (Array a, Array a)))
copy2 xi yi n = Unsafe.toLinear (\xs -> Unsafe.toLinear (\ys -> (xs, copy xs xi ys yi n)))

  -- slices, splits, and appends

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

{-# INLINE splitAt #-}
{-@ reflect splitAt @-}
{-@ splitAt :: m:Nat -> { xs:_  | m <= size xs }
                     -> { tup:_ | size (fst tup) == m           && token (fst tup) == token xs &&
                                  left (fst tup) == left xs     && right (fst tup) == left xs + m &&
                                  size (snd tup) == size xs - m && token (snd tup) == token xs &&
                                  left (snd tup) == left xs + m && right (snd tup) == right xs &&
                                  fst tup == slice xs 0 m       && snd tup == slice xs m (size xs) } @-}
splitAt :: Int -> Array a -. (Array a, Array a)
splitAt m = Unsafe.toLinear (\xs -> (slice xs 0 m, slice xs m (size xs)))

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
append :: Array a -. Array a -. Array a
append = Unsafe.toLinear (\xs -> Unsafe.toLinear (\ys ->
  case (xs, ys) of ((Arr arr1 l1 _r1 t), (Arr arr2 _l2 r2 _t)) -> Arr (conc arr1 arr2) l1 r2 t))


--------------------------------------------------------------------------------
-- | Proofs
--------------------------------------------------------------------------------

{-@ lem_getList_conc_left :: xs:_ -> ys:_  -> { i:Nat | i < len xs }
        -> { pf:_ | getList (conc xs ys) i == getList xs i } @-}
lem_getList_conc_left :: [a] -> [a] -> Int -> Proof
lem_getList_conc_left (x:xs) ys 0 = ()
lem_getList_conc_left (x:xs) ys i = lem_getList_conc_left xs ys (i-1)

{-@ lem_getList_conc_right :: xs:_ -> ys:_
        -> { i:Nat | len xs <= i && i < len xs + len ys }
        -> { pf:_ | getList (conc xs ys) i == getList ys (i - len xs) } @-}
lem_getList_conc_right :: [a] -> [a] -> Int -> Proof
lem_getList_conc_right []     ys i = ()
lem_getList_conc_right (x:xs) ys i = lem_getList_conc_right xs ys (i-1)

{-@ lem_get_append_left :: xs:Array a
        -> { ys:Array a | token xs == token ys && right xs == left ys }
        -> { i:Nat | i < size xs }
        -> { pf:_  | get (append xs ys) i == get xs i } @-}
lem_get_append_left :: Array a -> Array a -> Int -> Proof
lem_get_append_left (Arr xls _ _ _) (Arr yls _ _ _) i
    = lem_getList_conc_left xls yls i

{-@ lem_get_append_right :: xs:Array a
        -> { ys:Array a | token xs == token ys && right xs == left ys }
        -> { i:Nat | size xs <= i && i < size xs + size ys }
        -> { pf:_  | get (append xs ys) i == get ys (i - size xs) } @-}
lem_get_append_right :: Array a -> Array a -> Int -> Proof
lem_get_append_right (Arr xls _ _ _) (Arr yls _ _ _) i
    = lem_getList_conc_right xls yls i

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

{-@ lem_setList_commute :: xs:_ -> i:Nat -> xi:_
        -> { j:Nat | i < j && j < len xs } -> xj:_
        -> { pf:_ | setList (setList xs j xj) i xi == setList (setList xs i xi) j xj } @-}
lem_setList_commute :: [a] -> Int -> a -> Int -> a -> Proof
lem_setList_commute (x:xs) 0 xi j xj = ()
lem_setList_commute (x:xs) i xi j xj = () ? lem_setList_commute xs (i-1) xi (j-1) xj

{-@ lem_set_commute :: xs:_ -> { i:Nat | i < size xs } -> xi:_
        -> { j:Nat | not (i = j) && j < size xs } -> xj:_
        -> { pf:_ | set (set xs j xj) i xi == set (set xs i xi) j xj } @-}
lem_set_commute :: Array a -> Int -> a -> Int -> a -> Proof
lem_set_commute (Arr arr _ _ _) i xi j xj
  | i < j     = () ? lem_setList_commute arr i xi j xj
  | otherwise = () ? lem_setList_commute arr j xj i xi

{-@ lem_setList_twice :: xs:_ -> { i:Nat | i < len xs } -> xi:_ -> xi':_
        -> { pf:_ | setList (setList xs i xi') i xi == setList xs i xi } @-}
lem_setList_twice :: [a] -> Int -> a -> a -> Proof
lem_setList_twice (x:xs) 0 xi xi' = ()
lem_setList_twice (x:xs) i xi xi' = () ? lem_setList_twice xs (i-1) xi xi'

{-@ lem_set_twice :: xs:_ -> { i:Nat | i < size xs } -> xi:_ -> xi':_
        -> { pf:_ | set (set xs i xi') i xi == set xs i xi } @-}
lem_set_twice :: Array a -> Int -> a -> a -> Proof
lem_set_twice (Arr arr _ _ _) i xi xi' = lem_setList_twice arr i xi xi'

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

{-@ lem_take_take :: xs:_ -> { i:Nat | i <= len xs } -> { j:Nat | j <= i }
                  -> { pf:_ | take j (take i xs) == take j xs } @-}
lem_take_take :: [a] -> Int -> Int -> Proof
lem_take_take _      i 0 = ()
lem_take_take (x:xs) i j = lem_take_take xs (i-1) (j-1)

{-@ lem_drop_take :: xs:_ -> { i:Nat | i <= len xs } -> { j:Nat | j <= i }
                  -> { pf:_ | drop j (take i xs) == take (i-j) (drop j xs) } @-}
lem_drop_take :: [a] -> Int -> Int -> Proof
lem_drop_take _      i 0 = ()
lem_drop_take (x:xs) i j = lem_drop_take xs (i-1) (j-1)

{-@ lem_drop_drop :: xs:_ -> { i:Nat | i <= len xs } -> { j:Nat | j <= len xs - i }
                  -> { pf:_ | drop j (drop i xs) == drop (j+i) xs } @-}
lem_drop_drop :: [a] -> Int -> Int -> Proof
lem_drop_drop _      0 j = ()
lem_drop_drop (x:xs) i j = lem_drop_drop xs (i-1) j

{-@ lem_get_slice :: xs:_ -> { l:Nat | l <= size xs } -> { r:Nat | l < r && r <= size xs }
                          -> { i:Nat | l <= i && i < r }
                          -> { pf:_ | get (slice xs l r) (i - l) == get xs i } @-}
lem_get_slice :: Array a -> Int -> Int -> Int -> Proof
lem_get_slice arr l r i = () ? lem_getList_take (drop l lst) (r - l) (i - l)
                             ? lem_getList_drop lst          l       i
  where
    lst = toList arr

{-@ lem_slice_append :: xs:_ -> { ys:_ | token xs == token ys && right xs == left ys }
                             -> { pf:_ | slice (append xs ys) 0 (size xs) == xs &&
                                         slice (append xs ys) (size xs) (size xs + size ys) == ys } @-}
lem_slice_append :: Array a -> Array a -> Proof
lem_slice_append (Arr xls _ _ _) (Arr yls _ _ _)  = () ? lem_take_conc xls yls
                                                       ? lem_drop_conc xls yls
                                                       ? lem_take_all      yls

{- don't need this one i think
{-@ lem_slice_from_right_append :: xs:_
                      -> { ys:_ | token xs == token ys && right xs == left ys }
                      -> { i:Nat | A.size xs <= i }
                      -> { j:Nat | i <= j && j <= A.size xs + A.size ys }
                      -> { pf:_ | slice (append xs ys) i j == slice ys (i-size xs) (j-size xs)} @-}
lem_slice_from_right_append :: Array a -> Array a -> Proof
lem_slice_from_right_append (Arr xls _ _ _) (Arr yls _ _ _)
    = lem_drop_drop (conc xls yls) (len xls) (i - len xls)
    ? lem_drop_conc xls yls
-}

{-@ lem_slice_twice :: xs:_ -> i:Nat  -> { j:Nat  | i <= j && j <= size xs }
                              -> i':Nat -> { j':Nat | i' <= j' && j' <= j - i }
                              -> {pf:_ | slice (slice xs i j) i' j' == slice xs (i+i') (i+j') }
                               / [j' - i'] @-}
lem_slice_twice :: Eq a => Array a -> Int -> Int -> Int -> Int -> Proof
lem_slice_twice (Arr xs _ _ _)  i j i' j'
    | i' == j'  = ()
    | otherwise = lem_drop_take (drop i xs) (j-i) i'
                ? lem_drop_drop xs i i'
                ? lem_take_take (drop (i+i') xs) (j - i - i') (j' - i')
                -- LHS = take (j'-i') (drop i' (take (j-i) (drop i xs)))
                -- RHS = take (j'-i') (drop (i+i') xs)
