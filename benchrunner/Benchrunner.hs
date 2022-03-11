module Main where

import           Criterion          ( Benchmark, bench, bgroup, whnf, nf )
import           Criterion.Main     ( defaultMain )
import           Control.DeepSeq    ( NFData, force)
import           Data.Proxy         ( Proxy(..) )
import           Data.Int           ( Int64 )
import           Data.List.Split    ( splitOn )
import           System.Random      ( Random, newStdGen, randoms )
import           System.Environment ( getArgs, withArgs )

import qualified Insertion as I
import qualified QuickSort as Q
import qualified Merge as M
-- import qualified DpsMerge as DM
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
    pure $ bgroup "" $ map (go input (show input_size)) fns
  where
    go input str (name,fn) = bench (name ++ "/" ++ str) (nf fn input)

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
                (Proxy :: Proxy Int64)
                size
                [ ("LH/insertion1", I.isort1)
                -- , ("LH/insertion2", I.isort2)
                , ("LH/quick", Q.quickSort)
                , ("LH/merge", M.msort)
                -- , ("LH/dps_merge", DM.msort')
                ]
  withArgs rst $ defaultMain [ runbench ]
