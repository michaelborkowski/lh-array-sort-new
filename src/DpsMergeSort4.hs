{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wno-name-shadowing #-}

module DpsMergeSort4 where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import           Array as A
import           ArrayOperations
import           DpsMerge (merge)
import Properties.Equivalence
import Properties.Order

import           Linear.Common
#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
#else
import           Array.List as A
#endif

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
msortInplace :: (Show a, HasPrimOrd a) => A.Array a -. A.Array a -. (A.Array a, A.Array a)
msortInplace src tmp = go src tmp where
  {-@ go :: xs:Array a
        -> { ys:(Array a ) | A.size ys  == A.size xs   && left xs == left ys &&
                             right xs == right ys }
        -> (Array a, Array a)<{\zs ts -> toBag xs == toBag zs && isSorted' zs &&
                                         token xs == token zs && token ys == token ts &&
                                         A.size xs == A.size zs && A.size ys == A.size ts &&
                                         left zs == left xs && right zs == right xs &&
                                         left ts == left ys && right ts == right ys }>
         / [A.size xs] @-}
  go :: (Show a, HasPrimOrd a) => A.Array a -. A.Array a -. (A.Array a, A.Array a)
  go src tmp =
        let !(Ur len, src') = A.size2 src in
        if len <= 1 then (src', tmp)
        else
        let !(srcA, srcB)     = splitMid src'
            !(tmpA, tmpB)     = splitMid tmp
            !(src1, src2)     = splitMid srcA
            !(src3, src4)     = splitMid srcB
            !(tmp1, tmp2)     = splitMid tmpA
            !(tmp3, tmp4)     = splitMid tmpB
            !(src1', tmp1')   = go src1 tmp1
            !(src2', tmp2')   = go src2 tmp2
            !(src3', tmp3')   = go src3 tmp3
            !(src4', tmp4')   = go src4 tmp4
            tmpA'            = A.append tmp1' tmp2'
            tmpB'            = A.append tmp3' tmp4'
            !(srcA'', tmpA'') = merge src1' src2' tmpA'
            !(srcB'', tmpB'') = merge src3' src4' tmpB'
            src''            = A.append srcA'' srcB''
            !(tmp''', src''') = merge tmpA'' tmpB'' src''
        in (src''', tmp''')  ? lem_toBag_splitMid src
                                ? lem_toBag_splitMid tmp
                                ? lem_toBag_splitMid srcA
                                ? lem_toBag_splitMid srcB
                                ? lem_toBag_splitMid tmpA
                                ? lem_toBag_splitMid tmpB
{-# INLINE msortInplace #-}

{-@ msort' :: y:a
           -> { xs:(Array a) | A.size xs > 0 && left xs == 0 && right xs == size xs && y == A.get xs 0 }
           -> { zs:(Array a) | toBag xs == toBag zs && isSorted' zs &&
                               A.size xs == A.size zs && token xs == token zs } @-}
msort' :: (Show a, HasPrimOrd a) => a -> A.Array a -. A.Array a
msort' anyVal src =
  let !(Ur len, src') = A.size2 src
      !(src'', _tmp) = msortInplace src' (A.make len anyVal) in
  case A.free _tmp of !() -> src''
{-# INLINE msort' #-}

-- finally, the top-level merge sort function -- TODO: use A.get2/A.size2 for linearity
{-@ msort :: { xs:(A.Array a) | left xs == 0 && right xs == size xs }
                    -> { ys:_ | toBag xs == toBag ys && isSorted' ys &&
                                A.size xs == A.size ys && token xs == token ys  } @-}
msort :: (Show a, HasPrimOrd a) => A.Array a -. A.Array a
msort src =
  let !(Ur len, src') = A.size2 src in
      if len == 0 then src'
      else let !(Ur x0, src'') = A.get2 0 src' in msort' x0 src''
{-# INLINABLE msort #-}
