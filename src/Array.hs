{-# LANGUAGE CPP #-}

{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module Array
  (
    -- * Array type
    Array

    -- * Construction and querying
  , make, size, get, set, slice, append,    copy2

    -- * Linear versions
  ,      size2, get2,     slice2

    -- * Convert to/from lists
  , fromList, toList

    -- * Advanced operations
  , splitMid, swap

    -- * Parallel tuple operator
  , (.||.), tuple2, tuple4

    -- * LiqidHaskell lemmas
  , lma_gs, lma_gns, lma_swap, lma_swap_eql, lem_slice_append, lem_get_slice
  ) where

import           Prelude hiding (take, drop)
import           Array.List ( lma_gs_list, lma_gns_list
                            , lem_take_conc, lem_drop_conc, lem_take_all
                            , lem_getList_take, lem_getList_drop
                            , take, drop
                            )

#ifdef MUTABLE_ARRAYS
import           Array.Mutable
import           Control.DeepSeq ( NFData(..) )
import           Control.Parallel.Strategies (runEval, rpar, rseq)
import qualified Control.Monad.Par as P (runPar, spawnP, spawn_, get, fork, put, new)
#else
import           Array.List
#endif

import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators

--------------------------------------------------------------------------------

{-

[2022.06.23] CSK:
--------------------

Previously lem_slice_append and lem_get_slice were defined in this module and
they operated on the abstract Array type. All they did was call the corresponding
lemmas that work on lists, which are defined in Array.List. We were using toList
to convert the abstract array type to a list. But this was causing some problems
with LH (I think?). So their definitons were moved into Array.List. However, we
need these lemmas to be defined even when compiling with -fmutable-arrays since
some proofs in the the Equivalence module use them. I'm including the following
placeholder definitions to get the project to compile with -fmutable-arrays.
These won't pass the Liquid checker of course, so I'm disabling it for now.

Relevant commit:
https://github.com/ucsd-progsys/lh-array-sort/commit/6bd6b8936e3367a9365fc1f5cdf666f65b0575c7

-}

#ifdef MUTABLE_ARRAYS
lem_slice_append :: Array a -> Array a -> Proof
lem_slice_append = _todo

lem_get_slice :: Array a -> Int -> Int -> Int -> Proof
lem_get_slice = _todo
#endif

--------------------------------------------------------------------------------
-- tuple2 :: NFData a => (Array a -> (Array a, Array a)) -> Array a -> Array a
--               -> ( (Array a, Array a), (Array a, Array a))
-- tuple4 :: NFData a => (Array a -> (Array a, Array a))
--               -> Array a -> Array a -> Array a -> Array a
--               -> ( (Array a, Array a), (Array a, Array a), (Array a, Array a), (Array a, Array a))

-- This doesn't belong here, but it's here for convenience.

-- | Parallel tuple combinators.
--   The top level one should be .|*|. which rseqs before return
--   but .||. can be used to get more than 2 way parallelism
infixr 1 .||.
#ifdef MUTABLE_ARRAYS
tuple2 :: (NFData a, NFData b) => (a -> b) -> a -> (a -> b) -> a -> (b, b)
tuple2 f x g y = P.runPar $ do
                     fx  <- P.spawn_ $ return (f x)
                     gy  <- P.spawn_ $ return (g y)
                     fx' <- P.get fx
                     gy' <- P.get gy
                     return (fx', gy')

tuple4 :: (NFData a, NFData b) => (a -> b) -> a -> (a -> b) -> a
                               -> (a -> b) -> a -> (a -> b) -> a -> ((b, b), (b, b))
tuple4 f x g y h z j w = P.runPar $ do
                             fx  <- P.spawn_ $ return (f x)
                             gy  <- P.spawn_ $ return (g y)
                             hz  <- P.spawn_ $ return (h z)
                             jw  <- P.spawn_ $ return (j w)
                             fx' <- P.get fx
                             gy' <- P.get gy
                             hz' <- P.get hz
                             jw' <- P.get jw
                             return ((fx', gy'), (hz', jw'))

(.||.) :: (NFData a, NFData b) => a -> b -> (a,b)
{-  this is what we want to use, but doesn't run quite yet -}
a .||. b = P.runPar $ do          -- or P.spawn_ ?
               a'  <- P.spawnP a
               b'  <- P.spawnP b
               a'' <- P.get a'
               b'' <- P.get b'
               return (a'', b'') 
#else
{-@ tuple2 :: f:_ -> x:a -> g:_ -> y:a -> { tup:_ | fst tup == f x && snd tup == g y } @-} 
tuple2 :: (a -> b) -> a -> (a -> b) -> a -> (b, b)
tuple2 f x g y = (f x, g y)

{-@ tuple4 :: f:_ -> x:a -> g:_ -> y:a -> h:_ -> z:a -> j:_ -> w:a 
                  -> { tup:_ | fst (fst tup) == f x && snd (fst tup) == g y &&
                               fst (snd tup) == h z && snd (snd tup) == j w } @-}
tuple4 :: (a -> b) -> a -> (a -> b) -> a 
       -> (a -> b) -> a -> (a -> b) -> a -> ((b, b), (b, b))
tuple4 f x g y h z j w = ((f x, g y), (h z, j w))

{-@ (.||.) :: x:a -> y:b -> { tup:_ | x == fst tup && y = snd tup } @-}
(.||.) :: a -> b -> (a,b)
a .||. b = (a,b)
#endif

--------------------------------------------------------------------------------

-- advanced operations

{-@ reflect swap @-}
{-@ swap :: xs:(Array a) -> { i:Int | 0 <= i && i < size xs }
                         -> { j:Int | 0 <= j && j < size xs }
                         -> { ys:(Array a) | size xs == size ys && token xs == token ys &&
                                             left xs == left ys && right xs == right ys } @-}
swap :: Array a -> Int -> Int -> Array a
swap xs i j = let xi   = get xs i
                  xs'  = set xs i (get xs j)
                  xs'' = set xs' j xi
               in xs''


{-@ reflect splitMid @-}
{-@ splitMid :: xs:(Array a)
      -> {t:_ | token (fst t) == token xs && token (snd t) == token xs &&
                right (fst t) == left (snd t) &&
                right (fst t) == left xs + div (size xs) 2 &&
                left (fst t) == left xs && right (snd t) == right xs &&
                size (fst t) == div (size xs) 2 &&
                size (snd t) == size xs - div (size xs) 2 &&
                size xs = (size (fst t)) + (size (snd t)) } @-}
splitMid :: Ord a => Array a -> (Array a, Array a)
splitMid xs = (slice xs 0 m, slice xs m n)   
  where
    n = size xs
    m = n `div` 2

--------------------------------------------------------------------------------
-- | Proofs
--------------------------------------------------------------------------------

{-@ lma_gs :: xs:_ -> n:{v:Nat | v < size xs } -> x:_
      -> {pf:_ | get (set xs n x) n = x} @-}
lma_gs :: Array a -> Int -> a -> Proof
lma_gs arr n x = lma_gs_list (toList arr) n x

--{-@ lma_gs2 :: xs:_ -> n:{v:Nat | v < size xs } -> x:_
--      -> {pf:_ | fst (get2 (set xs n x) n) = x} @-}
--lma_gs2 :: Array a -> Int -> a -> Proof
--lma_gs2 xs n x = lma_gs xs n x

{-@ lma_gns :: xs:_ -> n:{v:Nat | v < size xs }
          -> m:{v:Nat | v /= n && v < size xs } -> x:_
          -> { pf:_ | get (set xs n x) m = get xs m} @-}
lma_gns :: Array a -> Int -> Int -> a -> Proof
lma_gns arr n m x = lma_gns_list (toList arr) n m x

--{-@ lma_gns2 :: xs:_ -> n:{v:Nat | v < size xs } 
--          -> m:{v:Nat | v /= n && v < size xs } -> x:_
--          -> { pf:_ | fst (get2 (set xs n x) m) == fst (get2 xs m) } @-}
--lma_gns2 :: Array a -> Int -> Int -> a -> Proof
--lma_gns2 xs n m x = lma_gns xs n m x


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

#ifndef MUTABLE_ARRAYS
{-@ lem_get_slice :: xs:_ -> { l:Nat | l <= size xs } -> { r:Nat | l < r && r <= size xs }
                          -> { i:Nat | l <= i && i < r }
                          -> { pf:_ | get (slice xs l r) (i - l) == get xs i } @-}
lem_get_slice :: Array a -> Int -> Int -> Int -> Proof
lem_get_slice arr l r i = () ? lem_getList_take (drop l lst) (r - l) (i - l)
                             ? lem_getList_drop lst          l       i
  where
    lst = toList arr
#endif
