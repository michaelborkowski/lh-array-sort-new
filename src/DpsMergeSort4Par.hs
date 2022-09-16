{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection"  @-}

{-# LANGUAGE CPP #-}

module DpsMergeSort4Par where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators hiding ((?))
import           ProofCombinators
import           Array 
import           DpsMergePar
import qualified DpsMergeSort4 as Seq
import           Equivalence
import           Order

#ifdef MUTABLE_ARRAYS
import           Array.Mutable as A
import           Control.DeepSeq ( NFData(..) )
#else
import           Array.List as A
#endif

#define KILO     1024
#define SEQSIZE  4096

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
msortInplace :: (Show a, Ord a, NFData a) => A.Array a -> A.Array a -> (A.Array a, A.Array a)
msortInplace src tmp =
  let (len, src') = A.size2 src in
  if len <= SEQSIZE
  then let (src'', tmp'') = Seq.msortInplace src' tmp
       in  (src'', tmp'')
  else
    let (srcA, srcB)     = splitMid src'
        (tmpA, tmpB)     = splitMid tmp
        (src1, src2)     = splitMid srcA
        (src3, src4)     = splitMid srcB
        (tmp1, tmp2)     = splitMid tmpA
        (tmp3, tmp4)     = splitMid tmpB
        (((src1', tmp1'), (src2', tmp2')), ((src3', tmp3'), (src4', tmp4'))) 
                         = tuple4 (msortInplace src1) tmp1 (msortInplace src2) tmp2
                                  (msortInplace src3) tmp3 (msortInplace src4) tmp4
--                         = (msortInplace src1 tmp1 .||. msortInplace src2 tmp2) .|*|.
  --                         (msortInplace src3 tmp3 .||. msortInplace src4 tmp4)
        tmpA'            = A.append tmp1' tmp2'
        tmpB'            = A.append tmp3' tmp4'
        ((srcA'', tmpA''), (srcB'', tmpB'')) 
                         = tuple2 (merge_par src1' src2') tmpA' (merge_par src3' src4') tmpB'
--                         = merge src1' src2' tmpA' .|*|. merge src3' src4' tmpB'
        src''            = A.append srcA'' srcB''
        (tmp''', src''') = merge_par tmpA'' tmpB'' src''
    in  (src''', tmp''') ? lem_toBag_splitMid src 
                         ? lem_toBag_splitMid tmp
                         ? lem_toBag_splitMid srcA
                         ? lem_toBag_splitMid srcB
                         ? lem_toBag_splitMid tmpA
                         ? lem_toBag_splitMid tmpB

{-@ msort' :: { xs:(Array a) | A.size xs > 0 && left xs == 0 && right xs == size xs }
           -> { y:a | y == A.get xs 0 }
           -> { zs:(Array a) | toBag xs == toBag zs && isSorted' zs &&
                               A.size xs == A.size zs && token xs == token zs } @-}
msort' :: (Show a, Ord a, NFData a) => A.Array a -> a -> A.Array a
msort' src anyVal =
  let (len, src') = A.size2 src
      (src'', _tmp) = msortInplace src' (A.make len anyVal) in
  {-_tmp `pseq`-} src''

-- finally, the top-level merge sort function -- TODO: use A.get2/A.size2 for linearity
{-@ msort :: { xs:(A.Array a) | left xs == 0 && right xs == size xs }
                    -> { ys:_ | toBag xs == toBag ys && isSorted' ys &&
                                A.size xs == A.size ys && token xs == token ys  } @-}
msort :: (Show a, Ord a, NFData a) => A.Array a -> A.Array a
msort src =
  let (len, src') = A.size2 src in
      if len == 0 then src'
      else let (x0, src'') = A.get2 src' 0 in msort' src'' x0
