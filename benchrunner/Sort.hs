-- | Encode sorting functions as an ADT
module Sort where

import Data.Int (Int64)
import Control.Monad.Primitive (PrimState)

import qualified Data.Vector.Unboxed as V
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

