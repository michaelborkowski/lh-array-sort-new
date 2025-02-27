
{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}


module DpsMergeSortPar where

import qualified Unsafe.Linear as Unsafe
import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import           Array as A
import           ArrayOperations
import           DpsMergePar
import qualified DpsMergeSort as Seq
--import qualified DpsMerge as Seq
import Properties.Equivalence
import Properties.Order
import           Par
import           Control.DeepSeq ( NFData(..) )

#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
#else
import           Array.List as A
#endif

#define KILO     1024
#define SEQSIZE  4096

--------------------------------------------------------------------------------

-- DPS mergesort
{-@ msortSwap :: xs:Array a
      -> { ys:(Array a ) | A.size ys  == A.size xs   && left xs == left ys &&
                           right xs == right ys }
      -> (Array a, Array a)<{\zs ts -> toBag xs == toBag ts && isSorted' ts &&
                                       token xs == token zs && token ys == token ts &&
                                       A.size xs == A.size zs && A.size ys == A.size ts &&
                                       left zs == left xs && right zs == right xs &&
                                       left ts == left ys && right ts == right ys }>
       / [A.size xs] @-}
msortSwap :: (Show a, HasPrimOrd a, NFData a) => A.Array a -> A.Array a -> (A.Array a, A.Array a)
msortSwap src tmp =
  let (len, src') = A.size2 src in
--  if len <= 1
--  then let !(src'', tmp'') = copy2_par src' 0 tmp 0 len in
--       (src'', tmp'')
  if len <= SEQSIZE
  then Seq.msortSwap src' tmp
  else
    let (src1, src2)  = splitMid src'
        (tmp1, tmp2)  = splitMid tmp
        ((src1', tmp1'), (src2', tmp2'))
--                      = tuple2 (msortInplace src1) tmp1 (msortInplace src2) tmp2
                      = msortInplace src1 tmp1 .||. msortInplace src2 tmp2
        !tmp3' = A.append tmp1' tmp2'
        !(src'', tmp4) = merge_par src1' src2' tmp3'
    in  (src'', tmp4)  ? lem_toBag_splitMid src -- tmp4 holds the sorted data
                       ? lem_toBag_splitMid tmp

{-@ msortInplace :: xs:Array a
      -> { ys:(Array a ) | A.size ys  == A.size xs   && left xs == left ys &&
                      right xs == right ys }
      -> { out:(Array a, Array a) | toBag xs == toBag (fst out) && isSorted' (fst out) &&
                                    token xs == token (fst out) && token ys == token (snd out) &&
                                    A.size xs == A.size (fst out) && A.size ys == A.size (snd out) &&
                                    left (fst out) == left xs && right (fst out) == right xs &&
                                    left (snd out) == left ys && right (snd out) == right ys }
       / [A.size xs] @-}
msortInplace :: (Show a, HasPrimOrd a, NFData a) => A.Array a -> A.Array a -> (A.Array a, A.Array a)
msortInplace src tmp =
  let (len, src') = A.size2 src in
  if len <= SEQSIZE
  then Seq.msortInplace src' tmp
  else
    let (src1, src2)   = splitMid src'
        (tmp1, tmp2)   = splitMid tmp
        ((src1', tmp1'), (src2', tmp2'))
--                       = tuple2 (msortSwap src1) tmp1 (msortSwap src2) tmp2
                       = msortSwap src1 tmp1 .||. msortSwap src2 tmp2
        !src3' = A.append src1' src2'
        !(tmp'', src4') = merge_par tmp1' tmp2' src3'
    in  (src4', tmp'')  ? lem_toBag_splitMid src -- src4' holds the sorted data
                        ? lem_toBag_splitMid tmp

{-@ msort' :: { xs:(Array a) | A.size xs > 0 && left xs == 0 && right xs == size xs }
           -> { y:a | y == A.get xs 0 }
           -> { zs:(Array a) | toBag xs == toBag zs && isSorted' zs &&
                               A.size xs == A.size zs && token xs == token zs } @-}
msort' :: (Show a, HasPrimOrd a, NFData a) => A.Array a -> a -> A.Array a
msort' src anyVal =
  let (n, src1) = A.size2 src
      {-@ promise :: { tmp:(Array a) | size tmp == n && left tmp == 0 && right tmp == n }
              -> { out:(Ur (Array a, Array a)) | toBag src == toBag (fst (unur out)) &&
                                                 isSorted' (fst (unur out)) &&
                    token src == token (fst (unur out)) && token tmp == token (snd (unur out)) &&
                    size (fst (unur out)) == n && size (snd (unur out)) == n } @-}
      promise tmp = Ur (msortInplace src1 tmp)
      Ur (src2, _tmp) = A.alloc n anyVal (Unsafe.toLinear promise) in
  _tmp `seq` src2

-- finally, the top-level merge sort function
{-@ msort :: { xs:(A.Array a) | left xs == 0 && right xs == size xs }
                    -> { ys:_ | toBag xs == toBag ys && isSorted' ys &&
                                A.size xs == A.size ys  } @-}
{- # SPECIALISE msort :: A.Array Float -> A.Array Float #-}
{- # SPECIALISE msort :: A.Array Int -> A.Array Int #-}
msort :: (Show a, HasPrimOrd a, NFData a) => A.Array a -> A.Array a
msort src =
  let (n, src1) = A.size2 src in
      if n == 0 then src1
      else let (x0, src2) = A.get2 src1 0
               {-@ promise :: { tmp:(Array a) | size tmp == n && left tmp == 0 && right tmp == n }
                           -> { out:(Ur (Array a)) | size (unur out) == n &&
                                                     left (unur out) == 0 && right (unur out) == n &&
                                                     toSlice (unur out) 0 n == toSlice src2 0 n} @-}
               promise tmp = Ur (A.copy src2 0 tmp 0 n)
                           ? lem_copy_equal_slice  src2 0 tmp 0 n
               {-@ cpy :: { ys:(Array a) | size ys == n && left ys == 0 && right ys == n &&
                                           toSlice ys 0 n == toSlice src2 0 n } @-}
               Ur cpy = A.alloc n x0 (Unsafe.toLinear promise)
           in msort' (cpy ? lem_equal_slice_bag   src2   cpy 0 n) x0
