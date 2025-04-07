-- | Kitchen sink
module Utils where

import qualified Array as A
import System.Random (Random, randoms, newStdGen)
import Control.DeepSeq (NFData, force)
import qualified Data.Primitive.Types as P
import Data.Proxy (Proxy)
import Control.Monad
import qualified Data.List as L

-- List utils

median :: [Double] -> Double
median ls = (L.sort ls) !! (length ls `div` 2)

-- |See 'Data.List.unfoldr'.  This is a monad-friendly version of that.
unfoldrM :: (Monad m) => (a -> m (Maybe (b, a))) -> a -> m [b]
unfoldrM f = go
  where
    go z = do
      x <- f z
      case x of
        Nothing -> return mzero
        Just (x', z') -> do
          xs <- go z'
          return (return x' `mplus` xs)

isSorted :: Ord a => [a] -> Bool
isSorted []       = True
isSorted [_]      = True
isSorted (x:y:xs) = x <= y && isSorted (y:xs)

-- Random stuff

randArray :: forall a. (Random a, NFData a, P.Prim a) => Proxy a -> Int -> IO (A.Array a)
randArray _ty size = do
  rng <- newStdGen
  let ls :: [a]
      ls = take size $ randoms rng
      !arr = force (A.fromList ls)
  pure arr

randList :: forall a. (Random a, NFData a) => Proxy a -> Int -> IO [a]
randList _ty size = do
  rng <- newStdGen
  let ls :: [a]
      ls = take size $ randoms rng
  pure (force ls)

-- Array / IO stuff
--
-- In benchrunner, we don't use the linear part of the Array interface,
-- so, we need means to sequentialize operations to not get into a pickle.
-- The easiest solution is to pretend to do IO.

copyArrayIO :: A.HasPrim a => A.Array a -> IO (A.Array a)
copyArrayIO arr = pure (A.copy arr 0 (A.make (A.size arr) (A.get arr 0)) 0 (A.size arr))
{-# NOINLINE copyArrayIO #-}

copyArrayInplaceIO :: A.HasPrim a => A.Array a -> A.Array a -> IO (A.Array a)
copyArrayInplaceIO src dst = pure (A.copy src 0 dst 0 (A.size src))
{-# NOINLINE copyArrayInplaceIO #-}
