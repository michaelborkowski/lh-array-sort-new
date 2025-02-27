
{-# LANGUAGE CPP #-}

module CilkSort where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import           Array
import           ArrayOperations
import           DpsMerge
import Properties.Equivalence
import Properties.Order
import           Insertion
import           QuickSortCilk

#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
#else
import           Array.List as A
#endif

#define KILO 1024
#define MERGESIZE (2*KILO)
#define QUICKSIZE (2*KILO)
#define INSERTIONSIZE 20

-- DPS mergesort -- unfold twice, merge twice
{-@ cilkSortInplace :: xs:Array a
      -> { ys:(Array a ) | A.size ys  == A.size xs   && left xs == left ys &&
                           right xs == right ys }
      -> (Array a, Array a)<{\zs ts -> toBag xs == toBag zs && isSorted' zs &&
                                       token xs == token zs && token ys == token ts &&
                                       A.size xs == A.size zs && A.size ys == A.size ts &&
                                       left zs == left xs && right zs == right xs &&
                                       left ts == left ys && right ts == right ys }>
       / [A.size xs] @-}
cilkSortInplace :: (Show a, Ord a) => A.Array a -> A.Array a -> (A.Array a, A.Array a)
cilkSortInplace src tmp =
  let (len, src') = A.size2 src in
  if len <= QUICKSIZE
  then let src'' = quickSort src'
        in (src'', tmp)
  else
    let (srcA, srcB)     = splitMid src'
        (tmpA, tmpB)     = splitMid tmp
        (src1, src2)     = splitMid srcA
        (src3, src4)     = splitMid srcB
        (tmp1, tmp2)     = splitMid tmpA
        (tmp3, tmp4)     = splitMid tmpB
        (src1', tmp1')   = cilkSortInplace src1 tmp1
        (src2', tmp2')   = cilkSortInplace src2 tmp2
        (src3', tmp3')   = cilkSortInplace src3 tmp3
        (src4', tmp4')   = cilkSortInplace src4 tmp4
        tmpA'            = A.append tmp1' tmp2'
        tmpB'            = A.append tmp3' tmp4'
        (srcA'', tmpA'') = merge src1' src2' tmpA'
        (srcB'', tmpB'') = merge src3' src4' tmpB'
        src''            = A.append srcA'' srcB''
        (tmp''', src''') = merge tmpA'' tmpB'' src''
    in (src''', tmp''')  ? lem_toBag_splitMid src
                         ? lem_toBag_splitMid tmp
                         ? lem_toBag_splitMid srcA
                         ? lem_toBag_splitMid srcB
                         ? lem_toBag_splitMid tmpA
                         ? lem_toBag_splitMid tmpB

{-@ cilkSort' :: { xs:(Array a) | A.size xs > 0 && left xs == 0 && right xs == size xs }
              -> { y:a | y == A.get xs 0 }
              -> { zs:(Array a) | toBag xs == toBag zs && isSorted' zs &&
                                  A.size xs == A.size zs && token xs == token zs } @-}
cilkSort' :: (Show a, Ord a) => A.Array a -> a -> A.Array a
cilkSort' src anyVal =
  let (len, src') = A.size2 src
      (src'', _tmp) = cilkSortInplace src' (A.make len anyVal) in
  _tmp `seq` src''

{-@ cilkSort :: { xs:(A.Array a) | left xs == 0 && right xs == size xs }
                    -> { ys:_ | toBag xs == toBag ys && isSorted' ys &&
                                A.size xs == A.size ys && token xs == token ys  } @-}
cilkSort :: (Show a, Ord a) => A.Array a -> A.Array a
cilkSort src =
  let (len, src') = A.size2 src in
      if len == 0 then src'
      else let (x0, src'') = A.get2 src' 0 in cilkSort' src'' x0
