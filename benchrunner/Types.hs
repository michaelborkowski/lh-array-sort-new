module Types (SortAlgo(..), Benchmark(..), ParOrSeq(..), Input(..), MVec, Vec, VecSort) where

import Data.Int (Int64)
import Control.Monad.Primitive (PrimState)

import qualified Array as A
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Unboxed.Mutable as MV

import Options.Generic

data SortAlgo
  = Insertionsort
  | Mergesort
  | Quicksort
  | Optsort -- piecewise fallback
  deriving (Eq, Show, Read, Generic)

modifiers :: Modifiers
modifiers = defaultModifiers
    { constructorNameModifier = id }

instance ParseRecord SortAlgo where
  parseRecord = parseRecordWithModifiers modifiers

instance ParseFields SortAlgo where
     parseFields = parseRecordWithModifiers modifiers

instance ParseRecord Benchmark where
  parseRecord = parseRecordWithModifiers modifiers

data Benchmark
  = GenerateArray
  | FillArray
  | CopyArray
  | SumArray
  | Fib
  | OurSort SortAlgo
  | VectorSort SortAlgo
  | CSort SortAlgo
  deriving (Eq, Show, Read, Generic)

data ParOrSeq = Seq | Par | ParM
  deriving (Eq, Show, Read, Generic)

data Input a
  = EltsIn
     Int {- number of elements -}
     a   {- element            -}
  | ArrayIn (A.Array a)
  | IntIn Int
  deriving Show

type MVec = MV.MVector (PrimState IO) Int64
type Vec = V.Vector Int64
type VecSort = MVec -> IO ()


-- instance ParseRecord ParOrSeq
