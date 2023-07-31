{-# LANGUAGE CPP           #-}
{-# LANGUAGE BangPatterns  #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LinearTypes   #-}
{-# LANGUAGE ConstraintKinds #-}
-- {-# LANGUAGE Strict        #-}

{-@ LIQUID "--reflection"  @-}
-- {-@ LIQUID "--diff"        @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorder" @-}

module Array
  (
    -- * Array type
    Array

    -- * Construction and querying
  , alloc, make, generate, generate_par, generate_par_m
  , copy, copy_par, copy_par_m
  , size, get, set, slice, append, splitMid, swap

    -- * Linear versions
  , size2, get2, slice2, copy2, copy2_par, swap2

    -- * Convert to/from lists
  , fromList, toList

  , Ur(..), unur

  , HasPrimOrd(..)

    -- * LiqidHaskell lemmas
  , lma_gs, lma_gns, lma_swap, lma_swap_eql, lem_swap_order
  , lem_slice_append, lem_get_slice

#ifdef MUTABLE_ARRAYS
  , module Array.Mutable
#else
  , module Array.List
#endif

  ) where

import qualified UnsafeLinear as Unsafe
import           Data.Unrestricted.Linear (Ur(..))
import           Prelude hiding (take, drop, splitAt)
import           GHC.Conc ( numCapabilities, par, pseq )
import           Array.List ( lma_gs_list, lma_gns_list
                            , lem_take_conc, lem_drop_conc, lem_take_all
                            , lem_getList_take, lem_getList_drop
                            , take, drop
                            )
import           Control.Parallel.Strategies (runEval, rpar, rseq)
import qualified Control.Monad.Par as P (Par, runPar, spawnP, spawn_, get, fork, put, new)

#ifdef MUTABLE_ARRAYS
import           Array.Mutable
#else
import           Array.List
#endif

import           Control.DeepSeq ( NFData(..) )
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import qualified Data.Primitive.Types as P

{-@ measure unur @-}
unur :: Ur a %1-> a
unur (Ur a) = a

--------------------------------------------------------------------------------
-- Advanced operations
--------------------------------------------------------------------------------

type HasPrimOrd a =
#ifdef PRIM_MUTABLE_ARRAYS
  (P.Prim a, Ord a)
#else
  (Ord a)
#endif


{-# INLINE alloc #-}
{-@ alloc :: forall <p :: Ur b -> Bool>. n:Nat -> x:_ 
                -> f:({ys:(Array a) | size ys == n} -> Ur<p> b) -> ret:Ur<p> b @-}
alloc ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Int -> a -> (Array a %1-> Ur b) %1-> Ur b
#ifdef MUTABLE_ARRAYS
alloc i a f = f (makeNoFill i a)
#else
alloc i a f = f (make i a)
#endif

-- with a concrete `b` type
{- @ alloc1 :: forall <p :: Ur (Array a) -> Bool>. n:Nat -> x:_ 
           -> f:({ys:(Array a) | size ys == n} 
                     -> {zs:(Ur<p> (Array a)) | size (unur zs) == n}) 
           -> { ret:(Ur<p> (Array a)) | size (unur ret) == n } @-}

{-@ reflect swap @-}
{-@ swap :: xs:(Array a) -> { i:Int | 0 <= i && i < size xs }
                         -> { j:Int | 0 <= j && j < size xs }
                         -> { ys:(Array a) | size xs == size ys && token xs == token ys &&
                                             left xs == left ys && right xs == right ys } @-}
swap ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> Int -> Int -> Array a
swap xs i j = let !xi   = get xs i
                  !xj   = get xs j
                  xs'   = set xs i xj
                  xs''  = set xs' j xi
#ifdef MUTABLE_ARRAYS
              in  xs' `pseq` xs''
#else
              in xs''
#endif

{-@ swap2 :: xs:(Array a) -> { i:Int | 0 <= i && i < size xs }
                          -> { j:Int | 0 <= j && j < size xs }
                          -> { ys:(Array a) | size xs == size ys && token xs == token ys &&
                                              left xs == left ys && right xs == right ys &&
                                              ys == swap xs i j } @-}
swap2 ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> Int -> Int -> Array a
swap2 xs i j  = {-Unsafe.toLinear3-} go xs i j
  where
    {-@ go :: xs:(Array a) -> { i:Int | 0 <= i && i < size xs }
                           -> { j:Int | 0 <= j && j < size xs }
                           -> { ys:(Array a) | size xs == size ys && token xs == token ys &&
                                               left xs == left ys && right xs == right ys &&
                                               ys == swap xs i j } @-}
    go xs i j =
      let (!xi, !xs1) = get2 xs i
          (!xj, !xs2) = get2 xs1 j
          !xs3 = set xs2 i xj
          !xs4 = set xs3 j xi
      in xi `pseq` xj `pseq` xs4
        -- (set xs2 i xj) `pseq` (set xs2 j xi)


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
splitMid = {- Unsafe.toLinear -} go
  where
    {-@ go :: xs:(Array a)
          -> {t:_ | token (fst t) == token xs && token (snd t) == token xs &&
                    right (fst t) == left (snd t) &&
                    right (fst t) == left xs + div (size xs) 2 &&
                    left (fst t) == left xs && right (snd t) == right xs &&
                    size (fst t) == div (size xs) 2 &&
                    size (snd t) == size xs - div (size xs) 2 &&
                    size xs = (size (fst t)) + (size (snd t)) } @-}
    go xs = (slice xs 0 m, slice xs m n)
      where
        n = size xs
        m = n `div` 2

--------------------------------------------------------------------------------
-- Parallel operations
--------------------------------------------------------------------------------

-- Same default as Cilk.
{-@ ignore defaultGrainSize @-}
defaultGrainSize :: Int -> Int
{-# INLINE defaultGrainSize #-}
defaultGrainSize n =
    let p = numCapabilities
        grain = max 1 (n `div` (8 * p))
    in min 2048 grain

{-@ ignore generate_par @-}
generate_par ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Int -> (Int -> a) -> Array a
{-# INLINE generate_par #-}
generate_par n f =
    let n'  = n `max` 0
        arr  = make n' (f 0)
        -- cutoff = defaultGrainSize n'
        cutoff = 4096
    in go cutoff arr
  where
    go !cutoff !arr =
      let n = size arr in
        if n <= cutoff
        then generate_loop arr 0 n f
        else
          let !mid  = n `div` 2
              (left, right) = splitAt mid arr
              arr1 = go cutoff left
              arr2 = go cutoff right
          in arr1 `par` arr2 `pseq` append arr1 arr2

{-@ ignore generate_par_m @-}
generate_par_m ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Int -> (Int -> a) -> P.Par (Array a)
{-# INLINE generate_par_m #-}
generate_par_m n f =
    let n'  = n `max` 0
        arr  = make n' (f 0)
        -- cutoff = defaultGrainSize n'
        cutoff = 4096
    in go cutoff arr
  where
    go !cutoff !arr =
      let n = size arr in
        if n <= cutoff
        then pure $ generate_loop arr 0 n f
        else do
          let !mid  = n `div` 2
              (left, right) = splitAt mid arr
          !arr1_f <- P.spawn_$ go cutoff left
          !arr2 <- go cutoff right
          !arr1 <- P.get arr1_f
          pure $ append left right

{-@ ignore generate @-}
generate ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Int -> (Int -> a) -> Array a
{-# INLINE generate #-}
generate n f =
    let n'  = n `max` 0
        arr = make n' (f 0)
    in generate_loop arr 0 n' f

{-@ ignore generate_loop @-}
generate_loop ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> Int -> Int -> (Int -> a) -> Array a
generate_loop arr idx end f =
    if idx == end
    then arr
    else let arr1 = set arr idx (f idx)
         in generate_loop arr1 (idx+1) end f

{-@ ignore copy2_par @-}
{- @ copy2_par :: xs:_ -> { xi:Nat | xi <= size xs } -> ys:_
              -> { yi:Nat | yi <= size ys }
              -> { n:Nat  | xi + n <= size xs && yi + n <= size ys }
              -> { zs:_   | xs == fst zs && snd zs == copy xs xi ys yi n &&
                            size (snd zs) == size ys && token (snd zs) == token ys &&
                            left (snd zs) == left ys && right (snd zs) == right ys } @-}
copy2_par ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> Int -> Array a -> Int -> Int -> (Array a, Array a)
copy2_par src0 src_offset0 dst0 dst_offset0 len0 = (src0, copy_par src0 src_offset0 dst0 dst_offset0 len0)

--TODO: src_offset0 and dst_offset0 are not respected.
{-@ ignore copy_par @-}
{- @ copy_par :: xs:_ -> { xi:Nat | xi <= size xs } -> ys:_
              -> { yi:Nat | yi <= size ys } 
              -> { n:Nat  | xi + n <= size xs && yi + n <= size ys }
              -> { zs:_   | zs == copy xs xi ys yi n &&
                            size ys == size zs && token ys == token zs &&
                            left ys == left zs && right ys == right zs }  @-}
copy_par ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> Int -> Array a -> Int -> Int -> Array a
copy_par src0 src_offset0 dst0 dst_offset0 len0 = copy_par' src0 src_offset0 dst0 dst_offset0 len0
  where
    cutoff = defaultGrainSize len0
    copy_par' !src src_offset !dst dst_offset !len =
      if len <= 1000000
      then copy src src_offset dst dst_offset len
      else let !half = len `div` 2
               !(src_l, src_r) = splitAt half src
               !(dst_l, dst_r) = splitAt (len-half) dst
               left = copy_par' src_l 0 dst_l 0 half
               right = copy_par' src_r 0 dst_r 0 (len-half)
           in left `par` right `pseq` append left right

--TODO: src_offset0 and dst_offset0 are not respected.
{-@ ignore copy_par_m @-}
copy_par_m ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> Int -> Array a -> Int -> Int -> P.Par (Array a)
copy_par_m !src0 src_offset0 !dst0 dst_offset0 !len0 = copy_par_m' src0 src_offset0 dst0 dst_offset0 len0
  where
    cutoff = defaultGrainSize len0
    copy_par_m' !src src_offset !dst dst_offset !len =
      if len <= 1000000
      then pure $ copy src src_offset dst dst_offset len
      else do
           let !half = len `div` 2
               !(src_l, src_r) = splitAt half src
               !(dst_l, dst_r) = splitAt (len-half) dst
           !left_f <- P.spawn_$ copy_par_m' src_l 0 dst_l 0 half
           !right <- copy_par_m' src_r 0 dst_r 0 (len-half)
           !left <- P.get left_f
           pure $ append left right

{-@ ignore foldl1_par @-}
foldl1_par :: Int -> (a -> a -> a) -> a -> Array a -> a
foldl1_par = _todo

-- (?) how do we do parallel fill array?
{-@ ignore make_par @-}
make_par :: Int -> a -> Array a
make_par = _todo

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
-- | Proofs
--------------------------------------------------------------------------------

{-@ lma_gs :: xs:_ -> n:{v:Nat | v < size xs } -> x:_
      -> {pf:_ | get (set xs n x) n = x} @-}
lma_gs ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> Int -> a -> Proof
lma_gs arr n x = lma_gs_list (toList arr) n x

--{-@ lma_gs2 :: xs:_ -> n:{v:Nat | v < size xs } -> x:_
--      -> {pf:_ | fst (get2 (set xs n x) n) = x} @-}
--lma_gs2 :: Array a -> Int -> a -> Proof
--lma_gs2 xs n x = lma_gs xs n x

{-@ lma_gns :: xs:_ -> n:{v:Nat | v < size xs }
          -> m:{v:Nat | v /= n && v < size xs } -> x:_
          -> { pf:_ | get (set xs n x) m = get xs m} @-}
lma_gns ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> Int -> Int -> a -> Proof
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
lma_swap ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> Int -> Int -> Proof
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
lma_swap_eql ::
#ifdef PRIM_MUTABLE_ARRAYS
  P.Prim a =>
#endif
  Array a -> Int -> Int -> Int -> Proof
lma_swap_eql xs i j k = () ? lma_gns xs' j k xi
                           ? lma_gns xs  i k (get xs j)
  where
    xi   = get xs  i
    xs'  = set xs  i (get xs j)

#ifndef MUTABLE_ARRAYS
{-@ lem_swap_order :: xs:(Array a) -> { i:Int | 0 <= i && i < size xs }
                        -> { j:Int | 0 <= j && j < size xs }
                        -> { pf:_ | swap xs i j == swap xs j i } @-}
lem_swap_order :: Array a -> Int -> Int -> Proof
lem_swap_order xs i j 
  | i == j    = ()
  | otherwise = () ? lem_set_commute xs i (get xs j) j (get xs i)

{-@ lem_get_slice :: xs:_ -> { l:Nat | l <= size xs } -> { r:Nat | l < r && r <= size xs }
                          -> { i:Nat | l <= i && i < r }
                          -> { pf:_ | get (slice xs l r) (i - l) == get xs i } @-}
lem_get_slice :: Array a -> Int -> Int -> Int -> Proof
lem_get_slice arr l r i = () ? lem_getList_take (drop l lst) (r - l) (i - l)
                             ? lem_getList_drop lst          l       i
  where
    lst = toList arr
#endif
