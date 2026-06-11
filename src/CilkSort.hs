
{-# LANGUAGE CPP #-}

module CilkSort where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators

import           ArrayOperations
import           Properties.Equivalence
import           Properties.Order
import           Par

import           DpsMergePar 
import qualified DpsMergeSort as Seq
import           Insertion
import           QuickSortCilk

import           Linear.Common
#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
import           Control.DeepSeq ( NFData(..) )
#else
import           Array.List as A
#endif
import           Array as A

#define KILO 1024
#define SEQSIZE   (4*KILO)
#define MERGESIZE (2*KILO)
#define QUICKSIZE (2*KILO)
#define INSERTIONSIZE 20

-- DPS mergesort -- unfold twice, merge twice
{-@ cilkSortInplace :: xs:Array a
      -> { ys:(Array a ) | A.size ys  == A.size xs   && left xs == left ys &&
                           right xs == right ys }
      -> ( {zs:(Array a) | toBag xs == toBag zs && isSorted' zs &&
                           token xs == token zs && A.size xs == A.size zs &&
                           left zs == left xs && right zs == right xs}
         , {ts:(Array a) | token ys == token ts && A.size ys == A.size ts &&
                           left ts == left ys && right ts == right ys} )
       / [A.size xs] @-}
#ifdef MUTABLE_ARRAYS
cilkSortInplace :: (Show a, HasPrimOrd a, NFData a) =>
#else
cilkSortInplace :: (Show a, HasPrimOrd a) =>
#endif
  A.Array a -. A.Array a -. (A.Array a, A.Array a)
cilkSortInplace src tmp = go src tmp where
  {-@ go :: xs:Array a
        -> { ys:(Array a ) | A.size ys  == A.size xs   && left xs == left ys &&
                             right xs == right ys }
        -> ( {zs:(Array a) | toBag xs == toBag zs && isSorted' zs &&
                             token xs == token zs && A.size xs == A.size zs &&
                             left zs == left xs && right zs == right xs}
           , {ts:(Array a) | token ys == token ts && A.size ys == A.size ts &&
                             left ts == left ys && right ts == right ys} )
        / [A.size xs] @-}
#ifdef MUTABLE_ARRAYS
  go :: (Show a, HasPrimOrd a, NFData a) =>
#else
  go :: (Show a, HasPrimOrd a) =>
#endif
    A.Array a -. A.Array a -. (A.Array a, A.Array a)
  go src tmp = 
    let !(Ur len, src') = A.size2 src in
    if len <= SEQSIZE
    then
      if len <= QUICKSIZE
      then let src'' = quickSort src'
            in (src'', tmp)
      else Seq.msortInplace src' tmp
    else
      let !(srcA, srcB)     = splitMid src'
          !(tmpA, tmpB)     = splitMid tmp
          !(src1, src2)     = splitMid srcA
          !(src3, src4)     = splitMid srcB
          !(tmp1, tmp2)     = splitMid tmpA
          !(tmp3, tmp4)     = splitMid tmpB
          !(((src1', tmp1'), (src2', tmp2')), ((src3', tmp3'), (src4', tmp4')))
                           = (go src1 tmp1 .||. go src2 tmp2) .||.
                             (go src3 tmp3 .||. go src4 tmp4)
          tmpA'            = A.append tmp1' tmp2'
          tmpB'            = A.append tmp3' tmp4'
          !((srcA'', tmpA''), (srcB'', tmpB''))
                           = merge_par src1' src2' tmpA' .||. merge_par src3' src4' tmpB'
          src''            = A.append srcA'' srcB''
          !(tmp''', src''') = merge_par tmpA'' tmpB'' src''
       in  (src''', tmp''') ? lem_toBag_splitMid src
                            ? lem_toBag_splitMid tmp
                            ? lem_toBag_splitMid srcA
                            ? lem_toBag_splitMid srcB
                            ? lem_toBag_splitMid tmpA
                            ? lem_toBag_splitMid tmpB
{-# INLINE cilkSortInplace #-}                            

{-@ cilkSort' :: y:a
           -> { xs:(Array a) | A.size xs > 0 && left xs == 0 && right xs == size xs && y == A.get xs 0 }
           -> { zs:(Array a) | toBag xs == toBag zs && isSorted' zs &&
                               A.size xs == A.size zs && token xs == token zs } @-}
#ifdef MUTABLE_ARRAYS
cilkSort' :: (Show a, HasPrimOrd a, NFData a) =>
#else
cilkSort' :: (Show a, HasPrimOrd a) =>
#endif
  a -> A.Array a -. A.Array a
cilkSort' anyVal src =
  let !(Ur len, src') = A.size2 src
      !src'' = A.allocScratch len anyVal cilkSortInplace src' in
  src''
{-# INLINE cilkSort' #-}  

{-@ cilkSort :: { xs:(A.Array a) | left xs == 0 && right xs == size xs }
                    -> { ys:_ | toBag xs == toBag ys && isSorted' ys &&
                                A.size xs == A.size ys && token xs == token ys  } @-}
cilkSort :: (Show a, Ord a) => A.Array a -> A.Array a
cilkSort src =
  let !(Ur len, src') = A.size2 src in
      if len == 0 then src'
      else let !(Ur x0, src'') = A.get2 0 src' in cilkSort' x0 src''
{-# INLINABLE cilkSort #-}
