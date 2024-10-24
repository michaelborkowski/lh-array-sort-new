
{-# LANGUAGE CPP #-}

module DpsMergeSort4Par where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import           Array as A
import           ArrayOperations
import           DpsMergePar
import qualified DpsMergeSort4 as Seq
import Properties.Equivalence
import Properties.Order
import           Par

import           Linear.Common
#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
import           Control.DeepSeq ( NFData(..) )
#else
import           Array.List as A
#endif

#define KILO     1024
#define SEQSIZE  4096

--------------------------------------------------------------------------------

-- DPS mergesort -- unfold twice, merge twice
{-@ msortInplace :: xs:Array a
      -> { ys:(Array a ) | A.size ys  == A.size xs   && left xs == left ys &&
                           right xs == right ys }
      -> (Array a, Array a)<{\zs ts -> toBag xs == toBag zs && isSorted' zs &&
                                       token xs == token zs && token ys == token ts &&
                                       A.size xs == A.size zs && A.size ys == A.size ts &&
                                       left zs == left xs && right zs == right xs &&
                                       left ts == left ys && right ts == right ys }>
       / [A.size xs] @-}
#ifdef MUTABLE_ARRAYS
msortInplace :: (Show a, HasPrimOrd a, NFData a) =>
#else
msortInplace :: (Show a, HasPrimOrd a) =>
#endif
  A.Array a -. A.Array a -. (A.Array a, A.Array a)
msortInplace src tmp =
  let !(Ur len, src') = A.size2 src in
  if len <= SEQSIZE
  then Seq.msortInplace src' tmp
  else
    let !(srcA, srcB)     = splitMid src'
        !(tmpA, tmpB)     = splitMid tmp
        !(src1, src2)     = splitMid srcA
        !(src3, src4)     = splitMid srcB
        !(tmp1, tmp2)     = splitMid tmpA
        !(tmp3, tmp4)     = splitMid tmpB
        !(((src1', tmp1'), (src2', tmp2')), ((src3', tmp3'), (src4', tmp4')))
                         = (msortInplace src1 tmp1 .||. msortInplace src2 tmp2) .||.
                           (msortInplace src3 tmp3 .||. msortInplace src4 tmp4)
--                         = tuple4 (msortInplace src1) tmp1 (msortInplace src2) tmp2
--                                  (msortInplace src3) tmp3 (msortInplace src4) tmp4
        tmpA'            = A.append tmp1' tmp2'
        tmpB'            = A.append tmp3' tmp4'
        !((srcA'', tmpA''), (srcB'', tmpB''))
                         = merge_par src1' src2' tmpA' .||. merge_par src3' src4' tmpB'
--                         = tuple2 (merge_par src1' src2') tmpA' (merge_par src3' src4') tmpB'
        src''            = A.append srcA'' srcB''
        !(tmp''', src''') = merge_par tmpA'' tmpB'' src''
    in  (src''', tmp''') ? lem_toBag_splitMid src
                         ? lem_toBag_splitMid tmp
                         ? lem_toBag_splitMid srcA
                         ? lem_toBag_splitMid srcB
                         ? lem_toBag_splitMid tmpA
                         ? lem_toBag_splitMid tmpB

{-@ msort' :: y:a
           -> { xs:(Array a) | A.size xs > 0 && left xs == 0 && right xs == size xs && y == A.get xs 0 }
           -> { zs:(Array a) | toBag xs == toBag zs && isSorted' zs &&
                               A.size xs == A.size zs && token xs == token zs } @-}
#ifdef MUTABLE_ARRAYS
msort' :: (Show a, HasPrimOrd a, NFData a) =>
#else
msort' :: (Show a, HasPrimOrd a) =>
#endif
  a -> A.Array a -. A.Array a
msort' anyVal src =
  let !(Ur len, src') = A.size2 src
      !(src'', _tmp) = msortInplace src' (A.make len anyVal) in
  case A.free _tmp of !() -> src''

-- finally, the top-level merge sort function
{-@ msort :: { xs:(A.Array a) | left xs == 0 && right xs == size xs }
                    -> { ys:_ | toBag xs == toBag ys && isSorted' ys &&
                                A.size xs == A.size ys && token xs == token ys  } @-}
#ifdef MUTABLE_ARRAYS
msort :: (Show a, HasPrimOrd a, NFData a) =>
#else
msort :: (Show a, HasPrimOrd a) =>
#endif
  A.Array a -. A.Array a
msort src =
  let !(Ur len, src') = A.size2 src in
      if len == 0 then src'
      else let !(Ur x0, src'') = A.get2 0 src' in msort' x0 src''
