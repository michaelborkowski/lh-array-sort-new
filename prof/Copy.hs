{-# LANGUAGE FlexibleContexts #-}

module Copy where

import qualified Array as A

import           Prelude
import           GHC.Conc

import           Debug.Trace
import           GHC.Stack
import           Data.List (intercalate)

import           Control.Monad.Primitive ( PrimMonad, PrimState )
import           Data.Foldable
import           Control.Monad.IO.Class
import qualified Control.Monad.Par as P
import           Control.Monad.Par.IO as ParIO
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Unboxed.Mutable as M

--------------------------------------------------------------------------------

copy2_parpseq :: A.Array a -> Int -> A.Array a -> Int -> Int -> (A.Array a, A.Array a)
copy2_parpseq = go
 where
  go :: A.Array a -> Int -> A.Array a -> Int -> Int -> (A.Array a, A.Array a)
  go src src_i dst dst_j n =
    if n <= 5000000
    then (A.copy2 src src_i dst dst_j n)
    else
      let mid = n `div` 2
          (src1, src2) = A.splitAt mid src
          (dst1, dst2) = A.splitAt mid dst
          ((src1', dst1'), (src2', dst2')) =
            (go src1 0 dst1 0 mid) .||. (go src2 0 dst2 0 (n - mid))
      in (A.append src1' src2', A.append dst1' dst2')


copy2_parmon :: A.Array a -> Int -> A.Array a -> Int -> Int -> P.Par (A.Array a, A.Array a)
copy2_parmon = go
 where
  go :: A.Array a -> Int -> A.Array a -> Int -> Int -> P.Par (A.Array a, A.Array a)
  go src src_i dst dst_j n =
    if n <= 5000000
    then pure (A.copy2 src src_i dst dst_j n)
    else do
      let mid = n `div` 2
      let (src1, src2) = A.splitAt mid src
          (dst1, dst2) = A.splitAt mid dst
      f1             <- P.spawn_ (go src1 0 dst1 0 mid)
      (src2', dst2') <- go src2 0 dst2 0 (n - mid)
      (src1', dst1') <- P.get f1
      pure (A.append src1' src2', A.append dst1' dst2')

{-# INLINE (.||.) #-}
(.||.) :: a -> b -> (a,b)
a .||. b = a `par` b `pseq` (a,b)



-- copyElems :: (M.Unbox a) => V.Vector a -> Int -> M.IOVector a -> Int -> Int -> IO ()
-- copyElems src src_i dst dst_j n =
--   let begin = 0
--       end = M.length src in
--   forM_ [begin..end-1] $ \i -> do
--     M.unsafeWrite dst (dst_j + i) $ (src `V.unsafeIndex` (src_i + i))

-- copy2_stdvec :: forall a. (M.Unbox a) => V.Vector a -> Int -> V.Vector a -> Int -> Int -> ParIO (V.Vector a, V.Vector a)
-- copy2_stdvec src src_i dst dst_j n = do
--      dst' <- liftIO $ V.unsafeThaw dst
--      (a,b) <- go src src_i dst' dst_j n
--      b' <- liftIO $ V.unsafeFreeze b
--      return (a,b)

--   where go :: V.Vector a -> Int -> V.Vector a -> Int -> Int -> ParIO (V.Vector a, V.Vector b)
--         go src src_i dst dst_j n
--           | n < 4096 = do
--             liftIO $ copyElems src src_i dst dst_j n
--             pure (src, dst)
--           | otherwise =
--             do let mid = n `div` 2
--                    (src_l,src_r) = V.splitAt mid src
--                    (dst_l,dst_r) = M.splitAt mid dst
--                f1 <- P.spawn_ $ go src_l 0 dst_l 0 mid
--                go src_r 0 dst_r 0 (n - mid)
--                P.get f1

{-
copy2_stdvec :: forall a. (PrimMonad ParIO, M.Unbox a) => V.Vector a -> Int -> V.Vector a -> Int -> Int -> ParIO (V.Vector a, V.Vector a)
copy2_stdvec src src_i dst dst_j n = do
  dst' <- V.unsafeThaw dst
  (a,b) <- go src src_i dst' dst_j n
  b' <- V.unsafeFreeze b
  return (a,b')
 where
  go :: V.Vector a -> Int -> M.MVector (PrimState ParIO) a -> Int -> Int
     -> ParIO (V.Vector a, M.MVector (PrimState ParIO) a)
  go src i dst j n
   | n < 4096 = do
       let begin = 0
           end = V.length src
       forM_ [begin..end-1] $ \i -> do
         M.unsafeWrite dst (dst_j + i) $ (src `V.unsafeIndex` (src_i + i))
       pure (src,dst)
   | otherwise = do
       let mid = n `div` 2
           (src_l,src_r) = V.splitAt mid src
           (dst_l,dst_r) = M.splitAt mid dst
       f1 <- P.spawn_ $ go src_l 0 dst_l 0 mid
       -- go src_r 0 dst_r 0 (n - mid)
       -- P.get f1
       undefined
-}
