{-# LANGUAGE CPP           #-}
{-# LANGUAGE BangPatterns  #-}
{-# LANGUAGE DeriveFunctor #-}


{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--higherorder" @-}

module ArrayOperations
  (
    -- * Construction and querying
    splitMid, swap

    -- * Linear versions
  , swap2

    -- * LiqidHaskell lemmas
  , lma_swap, lma_swap_eql, lem_swap_order
  ) where

import qualified Linear.Unsafe as Unsafe
import           Prelude hiding (take, drop, splitAt)
import           GHC.Conc ( numCapabilities, par, pseq )
import           Array
import           Control.Parallel.Strategies (runEval, rpar, rseq)
import qualified Control.Monad.Par as P (Par, runPar, spawnP, spawn_, get, fork, put, new)

import           Linear.Common
#ifdef MUTABLE_ARRAYS
import           Array.Mutable
#else
import           Array.List
#endif

import           Control.DeepSeq ( NFData(..) )
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import qualified Data.Primitive.Types as P
import qualified Array as key

--------------------------------------------------------------------------------
-- ArrayOperations contain Advanced Operations that live outside of the TCB
--    (so these are implemented once in terms of the TCB API)
--    and theorems about how they work.
--------------------------------------------------------------------------------

{-@ reflect swap @-}
{-@ swap :: xs:(Array a) -> { i:Int | 0 <= i && i < size xs }
                         -> { j:Int | 0 <= j && j < size xs }
                         -> { ys:(Array a) | size xs == size ys && token xs == token ys &&
                                             left xs == left ys && right xs == right ys } @-}
swap :: HasPrim a => Array a -> Int -> Int -> Array a
swap xs i j = let !xi   = get xs i
                  !xj   = get xs j
                  xs'   = set xs i xj
                  xs''  = set xs' j xi
#ifdef MUTABLE_ARRAYS
              in  xs' `pseq` xs''
#else
              in xs''
#endif

-- For correctness, the strictness annotations on !xi and !xj are crucial.
--   Due to laziness, there's otherwise nothing preventing `setLin i xj xs2`
--   from executing before `get2 i xs`. Same with `swap` above.
{-@ swap2 :: { i:Int | 0 <= i }
          -> { j:Int | 0 <= j } -> { xs:(Array a) | i < size xs && j < size xs }
          -> { ys:(Array a) | size xs == size ys && token xs == token ys &&
                              left xs == left ys && right xs == right ys &&
                              ys == swap xs i j } @-}
swap2 :: HasPrim a => Int -> Int -> (Array a -. Array a)
swap2 i j xs = 
  let
    !((Ur !xi), xs1) = get2 i xs
    !((Ur !xj), xs2) = get2 j xs1
    xs3 = setLin i xj xs2
    xs4 = setLin j xi xs3
  in {- xi `pseq` xj `pseq` -} xs4


{-@ reflect splitMid @-}
{-@ splitMid :: xs:(Array a)
      -> {t:_ | token (fst t) == token xs && token (snd t) == token xs &&
                right (fst t) == left (snd t) &&
                right (fst t) == left xs + div (size xs) 2 &&
                left (fst t) == left xs && right (snd t) == right xs &&
                size (fst t) == div (size xs) 2 &&
                size (snd t) == size xs - div (size xs) 2 &&
                size xs = (size (fst t)) + (size (snd t)) } @-}
splitMid :: {- Ord a => -} Array a -. (Array a, Array a)
splitMid = Unsafe.toLinear go
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
-- | Proofs
--------------------------------------------------------------------------------

{-@ lma_swap :: xs:(Array a) -> { i:Int | 0 <= i && i < size xs }
                             -> { j:Int | 0 <= j && j < size xs }
                             -> { pf:_  | get (swap xs i j) i == get xs j &&
                                          get (swap xs i j) j == get xs i } @-}
lma_swap :: HasPrim a => Array a -> Int -> Int -> Proof
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
lma_swap_eql :: HasPrim a => Array a -> Int -> Int -> Int -> Proof
lma_swap_eql xs i j k = () ? lma_gns xs' j k xi
                           ? lma_gns xs  i k (get xs j)
  where
    xi   = get xs  i
    xs'  = set xs  i (get xs j)

{-@ lem_swap_order :: xs:(Array a) -> { i:Int | 0 <= i && i < size xs }
                        -> { j:Int | 0 <= j && j < size xs }
                        -> { pf:_ | swap xs i j == swap xs j i } @-}
lem_swap_order :: Array a -> Int -> Int -> Proof
lem_swap_order xs i j
  | i == j    = ()
  | otherwise = () ? lem_set_commute xs i (get xs j) j (get xs i)
