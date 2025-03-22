-- | Encode sorting functions as an ADT
module Sort where

import qualified Insertion as I
import qualified QuickSort as Q
import qualified DpsMergeSort4 as DMS
import qualified DpsMergeSort4Par as DMSP
import qualified PiecewiseFallbackSort as PFS
import qualified PiecewiseFallbackSortPar as PFSP
import qualified Array as A
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Algorithms.Insertion as ISDVS
import qualified Data.Vector.Algorithms.Merge as MSDVS
import qualified Data.Vector.Algorithms.Intro as QSDVS

import Data.Int (Int64)
import Control.Monad.Primitive (PrimState)

import qualified Data.Vector.Unboxed.Mutable as MV
import qualified ForeignFunctionImports as FFI
import Control.DeepSeq (NFData)
import Linear.Common

data ParOrSeq = Seq | Par | ParM
  deriving (Eq, Show, Read)

data SortAlgo
  = Insertionsort
  | Mergesort
  | Quicksort
  | Optsort -- piecewise fallback
  deriving (Eq, Show, Read)

type MVec = MV.MVector (PrimState IO) Int64
type Vec = V.Vector Int64
type VecSort = MVec -> IO ()

sortFn :: (Show a, A.HasPrimOrd a, NFData a) => SortAlgo -> ParOrSeq -> (A.Array a -. A.Array a)
sortFn bench parorseq = case (bench,parorseq) of
  (Insertionsort, Seq) -> I.isort_top'
  (Quicksort, Seq)     -> Q.quickSort'
  (Mergesort, Seq) -> DMS.msort
  (Mergesort, Par) -> DMSP.msort
  (Optsort,   Seq) -> PFS.pfsort
  (Optsort,   Par) -> PFSP.pfsort
  oth -> error $ "sortFn: unknown configuration: " ++ show oth
{-# INLINABLE sortFn #-}

vectorSortFn :: SortAlgo -> ParOrSeq -> VecSort
vectorSortFn bench parorseq = case (bench,parorseq) of
  (Insertionsort, Seq) -> ISDVS.sort
  (Mergesort,     Seq) -> MSDVS.sort
  (Quicksort,     Seq) -> QSDVS.sort
  oth -> error $ "sortFn: unknown configuration: " ++ show oth
{-# INLINABLE vectorSortFn #-}

sortFnC :: SortAlgo -> FFI.SortFn
sortFnC alg = case alg of
                    Insertionsort -> FFI.c_insertionsort
                    Mergesort -> FFI.c_mergesort
                    Quicksort -> FFI.c_quicksort
                    _ -> error "sortFnC: Csort not implemented!"
{-# INLINABLE sortFnC #-}

sortFnCxx :: SortAlgo -> FFI.SortFnCxx
sortFnCxx alg = case alg of
                    Insertionsort -> FFI.cxx_int_insertionsort
                    Mergesort -> FFI.cxx_int_mergesort
                    Quicksort -> FFI.cxx_int_quicksort
                    _ -> error "sortFnCxx: Csort not implemented!"
{-# INLINABLE sortFnCxx #-}
