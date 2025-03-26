-- | Benchmarks and inputs

module Input where

import Sort
import Utils

import qualified Array as A
import qualified Vector as V

import Data.Proxy (Proxy (..))
import Data.Int (Int64)
import Text.Read

data Benchmark
  = GenerateArray
  | FillArray
  | CopyArray
  | SumArray
  | Fib
  | OurSort SortAlgo
  | VectorSort SortAlgo
  | CSort SortAlgo
  | CxxSort SortAlgo
  deriving (Eq, Show, Read)

readBench :: String -> Benchmark
readBench s = case readMaybe s of
  Just b -> b
  Nothing -> case readMaybe s of
    Just srt -> OurSort srt
    Nothing -> read s

data Input a
  = EltsIn
     Int {- number of elements -}
     a   {- element            -}
  | ArrayIn (A.Array a)
  | IntIn Int
  deriving Show

getInput :: Benchmark -> Maybe Int -> IO (Input Int64)
getInput bench mb_size = case bench of
  GenerateArray -> pure $ IntIn (mb 10000000)
  FillArray     -> pure $ EltsIn (mb 10000000) 1024
  CopyArray     -> pure $ ArrayIn (A.make (mb 10000000) 1)
  SumArray      -> pure $ ArrayIn (A.make (mb 10000000) 1)
  Fib           -> pure $ IntIn (mb 45)
  OurSort alg -> case alg of
    Insertionsort -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 100)
    Quicksort     -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 1000000)
    Mergesort     -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 8000000)
    Optsort       -> ArrayIn <$> randArray (Proxy :: Proxy Int64) (mb 8000000)
  _ -> error "getInput: Unexpected Input!"
  where
    mb x = case mb_size of
      Nothing -> x
      Just y  -> y

getInputAsDataVector :: SortAlgo -> Maybe Int -> IO Vec
getInputAsDataVector bench mb_size = case bench of
  Insertionsort -> V.fromList <$> randList (Proxy :: Proxy Int64) (mb 100)
  Quicksort -> V.fromList <$> randList (Proxy :: Proxy Int64) (mb 1000000)
  Mergesort -> V.fromList <$> randList (Proxy :: Proxy Int64) (mb 8000000)
  _ -> error "getInputAsDataVector: TODO sort function not implemented!"
  where
    mb x = case mb_size of
      Nothing -> x
      Just y -> y

getInputAsList :: SortAlgo -> Maybe Int -> IO [Int64]
getInputAsList bench mb_size = case bench of
  Insertionsort -> randList (Proxy :: Proxy Int64) (mb 100)
  Quicksort -> randList (Proxy :: Proxy Int64) (mb 1000000)
  Mergesort -> randList (Proxy :: Proxy Int64) (mb 8000000)
  _ -> error "getInputAsDataVector: TODO sort function not implemented!"
  where
    mb x = case mb_size of
      Nothing -> x
      Just y -> y
