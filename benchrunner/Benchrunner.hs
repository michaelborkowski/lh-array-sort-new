module Main where

import           Criterion          ( Benchmark, bench, bgroup, whnf, nf )
import           Criterion.Main     ( defaultMain )
import           Control.DeepSeq    ( NFData, force)
import           Data.Proxy         ( Proxy(..) )
import           Data.List.Split    ( splitOn )
import           System.Random      ( Random, newStdGen, randoms )
import           System.Environment ( getArgs, withArgs )

import qualified Insertion as I
import qualified QuickSort as Q
import qualified Merge as M
import qualified DpsMerge as DM
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
    pure $ bgroup (show input_size) $ map (go input) fns
  where
    go input (name,fn) = bench name (nf fn input)

main :: IO ()
main = do
  allargs <- getArgs
  let usage = "USAGE: benchrunner -- BENCH_ARGS -- CRITERION_ARGS"
      (size,rst) =
        case splitOn ["--"] allargs of
          [] -> (10,[])
          [(sz:_)] -> if sz == "--help"
                      then error usage
                      else (read sz :: Int, [])
          [(sz:_), rst'] -> if sz == "--help"
                            then error usage
                            else (read sz :: Int, rst')
          _ -> error usage
  runbench <- benchSorts
                (Proxy :: Proxy Int)
                size
                [ ("insertion", isort2)
                , ("quick", Q.quickSort)
                , ("merge", M.msort)
                , ("dps_merge", msort2)
                ]
  withArgs rst $ defaultMain [ runbench]
  where
    isort2 ls = I.isort ls (A.size ls - 1)
    msort2 ls = DM.msort ls (A.get ls 0)
