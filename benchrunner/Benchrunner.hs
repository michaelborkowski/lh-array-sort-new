module Main where

import           Criterion          ( Benchmark, bench, bgroup, whnf, nf )
import           Criterion.Main     ( defaultMain )
import           Control.DeepSeq    ( NFData, force)
import           Control.Monad      ( forM_, unless )
import           Data.Proxy         ( Proxy(..) )
import           Data.Int           ( Int64 )
import           Data.List.Split    ( splitOn )
import           System.Random      ( Random, newStdGen, randoms )
import           System.Environment ( getArgs, withArgs )

import qualified Insertion as I
import qualified QuickSort as Q
-- import qualified Merge as M
import qualified DpsMergeSort as DM
import qualified Array as A

--------------------------------------------------------------------------------

-- data SortAlgo = LH_Insertion
--               | LH_Quick

-- benchSorts :: (NFData a, Ord a) => Proxy a -> Int -> [SortAlgo] -> IO Benchmark
benchSorts :: forall a. (Random a, NFData a, Ord a) =>
              Proxy a -> Int -> [(String, A.Array a -> A.Array a)] -> IO Benchmark
benchSorts _input_ty input_size fns = do
    rng <- newStdGen
    let ls :: [a]
        ls = take input_size $ randoms rng
        !input = force (A.fromList ls)
    forM_ fns $ \(name,fn) ->
      unless (isSorted (A.toList $ fn input)) (error $ name ++ ": result not sorted.")
    pure $ bgroup "" $ map (go input (show input_size)) fns
  where
    go input str (name,fn) = bench (name ++ "/" ++ str) (nf fn input)

    isSorted :: Ord a => [a] -> Bool
    isSorted []       = True
    isSorted [_]      = True
    isSorted (x:y:xs) = x <= y && isSorted (y:xs)


bench_fill_array :: Int -> IO Benchmark
bench_fill_array input_size = do
  let input :: (Int, Int)
      !input = force (input_size, 1000)
  pure $ bgroup "" [ bench "fill_array" (nf fill input) ]
  where
    fill (s,x) = A.make s x

data Benchmarks = FillArray | Insertionsort | Mergesort
  deriving (Eq, Show, Read)

main :: IO ()
main = do
  allargs <- getArgs
  let usage = "USAGE: benchrunner -- BENCH_ARGS -- CRITERION_ARGS"
      (benchmark,size,rst) =
        case splitOn ["--"] allargs of
          [] -> (Insertionsort,10,[])
          [(bnch:sz:_)] -> if sz == "--help"
                      then error usage
                      else (read bnch :: Benchmarks, read sz :: Int, [])
          [(bnch:sz:_), rst'] -> if sz == "--help"
                            then error usage
                            else (read bnch :: Benchmarks, read sz :: Int, rst')
          _ -> error usage

  runbench <-
    case benchmark of
      FillArray -> bench_fill_array size
      Insertionsort ->
              benchSorts
                (Proxy :: Proxy Int64)
                size
                [ ("LH/insertion", I.isort_top) ]
      Mergesort ->
        benchSorts
                (Proxy :: Proxy Float)
                size
                [ ("LH/dps_merge", DM.msort) ]
  withArgs rst $ defaultMain [ runbench ]
