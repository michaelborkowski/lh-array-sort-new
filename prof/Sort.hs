{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash    #-}
{-# LANGUAGE Strict       #-}

module Sort where

import qualified Array as A

import           Prelude
import           GHC.Conc
-- import qualified Data.Vector.Unboxed as V
-- import qualified GHC.Exts as GHC

import           Debug.Trace
import           GHC.Stack
import           Data.List (intercalate)

import qualified Control.Monad.Par as P

--------------------------------------------------------------------------------

-- DPS mergesort
msortSwap :: (Show a, Ord a) => A.Array a -> A.Array a -> (A.Array a, A.Array a)
msortSwap !src !tmp =
  let !(len, src') = A.size2 src in
  if len == 1
  then let !(src'', tmp'') = A.copy2 src' 0 tmp 0 1 in
       (src'', tmp'')
  -- if len <= 2048
  -- then (isort2 src', tmp)
  else
    let (src1, src2) = A.splitMid src'
        (tmp1, tmp2) = A.splitMid tmp
        (src1', tmp1') = msortInplace src1 tmp1
        (src2', tmp2') = msortInplace src2 tmp2
        !tmp3' = A.append tmp1' tmp2'
        !(src'', tmp4) = merge src1' src2' tmp3'
    in (src'', tmp4)

msortInplace :: (Show a, Ord a) => A.Array a -> A.Array a -> (A.Array a, A.Array a)
msortInplace !src !tmp =
  let !(len, src') = A.size2 src in
  if len <= goto_isort
  then (isort2 src', tmp)
  -- if len == 1
  -- then (src', tmp)
  else
    let (src1, src2) = A.splitMid src'
        (tmp1, tmp2) = A.splitMid tmp
        (src1', tmp1') = msortSwap src1 tmp1
        (src2', tmp2') = msortSwap src2 tmp2
        !src3' = A.append src1' src2'
        !(tmp'', src4') = merge tmp1' tmp2' src3'
    in (src4', tmp'')

msort' :: (Show a, Ord a) => A.Array a -> a -> A.Array a
msort' src anyVal =
  let (len, src') = A.size2 src
      tmp = A.make len anyVal
      (src'', _tmp) = msortInplace src' tmp in
      -- src_copy = A.make len (A.get src 0)
      -- (_, src_copy') = A.copy2 src 0 src_copy 0 len
      -- (src'', _tmp) = msortInplace src_copy' tmp in
  _tmp `seq` src''

-- finally, the top-level merge sort function
{-# SPECIALISE msort :: A.Array Float -> A.Array Float #-}
{-# SPECIALISE msort :: A.Array Int -> A.Array Int #-}
msort :: (Show a, Ord a) => A.Array a -> A.Array a
msort src =
  let (len, src') = A.size2 src in
      if len == 0 then src'
      else let (x0, src'') = A.get2 src' 0 in msort' src'' x0


-- DPS merge
merge' :: (HasCallStack, Ord a, Show a) =>
  A.Array a -> A.Array a -> A.Array a ->
  Int -> Int -> Int ->
  (A.Array a, A.Array a)
merge' !src1 !src2 !dst i1 i2 j = -- traceShow ("merge", A.toList src1, A.toList src2, dst) $
  let !(len1, src1') = A.size2 src1
      !(len2, src2') = A.size2 src2 in
  if i1 >= len1
  then
    -- let (src2'1, dst') = copy src2' dst i2 j in (A.append src1' src2'1, dst')
    let !(src2'1, dst') = A.copy2 src2' i2 dst j (len2-i2)
    in -- traceShow ("copy", A.toList src2', (i2,j,len2-i2), dst') $
         (A.append src1' src2'1, dst')
  else if i2 >= len2
  then
    -- let (src1'1, dst') = copy src1' dst i1 j in (A.append src1'1 src2', dst')
    let !(src1'1, dst') = A.copy2 src1' i1 dst j (len1-i1)
    in -- traceShow ("copy", A.toList src1', (i1,j,len1-i1), dst') $
         (A.append src1'1 src2', dst')
  else
    let !(v1, src1'1) = A.get2 src1' i1
        !(v2, src2'1) = A.get2 src2' i2 in
    if v1 < v2
    then let dst' = A.set dst j  v1
             !(src'', dst'') =  merge' src1'1 src2'1 dst' (i1 + 1) i2 (j + 1) in
         (src'', dst'')
    else let dst' = A.set dst j v2
             !(src'', dst'') =  merge' src1'1 src2'1 dst' i1 (i2 + 1) (j + 1) in
         (src'', dst'')

{-# INLINE merge #-}
merge :: (HasCallStack, Ord a, Show a) => A.Array a -> A.Array a -> A.Array a -> (A.Array a, A.Array a)
merge src1 src2 dst = merge' src1 src2 dst 0 0 0

--------------------------------------------------------------------------------

-- DPS mergesort
msortSwap_par :: (Show a, Ord a) => A.Array a -> A.Array a -> P.Par (A.Array a, A.Array a)
msortSwap_par !src !tmp =
  let !(len, src') = A.size2 src in
  if len == 1
  -- then let (src'', tmp'') = copy src' tmp 0 0 in
  then do let !(src'', tmp'') = A.copy2 src' 0 tmp 0 1
          pure (src'', tmp'')
  else do
    let (src1, src2) = A.splitMid src'
        (tmp1, tmp2) = A.splitMid tmp

        -- (src1', tmp1') = msortInplace src1 tmp1
        -- (src2', tmp2') = msortInplace src2 tmp2
    f1 <- P.spawn_ (msortInplace_par src1 tmp1)
    f2 <- P.spawn_ (msortInplace_par src2 tmp2)
    (src1', tmp1') <- P.get f1
    (src2', tmp2') <- P.get f2

    let !tmp3' = A.append tmp1' tmp2'
    !(src'', tmp4) <- merge_par src1' src2' tmp3'
    pure (src'', tmp4)

msortInplace_par :: (Show a, Ord a) => A.Array a -> A.Array a -> P.Par (A.Array a, A.Array a)
msortInplace_par !src !tmp =
  let !(len, src') = A.size2 src in
  if len <= goto_isort
  then pure (isort2 src', tmp)
  else do
    let (src1, src2) = A.splitMid src'
        (tmp1, tmp2) = A.splitMid tmp

        -- (src1', tmp1') = msortSwap src1 tmp1
        -- (src2', tmp2') = msortSwap src2 tmp2
    f1 <- P.spawn_ (msortSwap_par src1 tmp1)
    f2 <- P.spawn_ (msortSwap_par src2 tmp2)
    (src1', tmp1') <- P.get f1
    (src2', tmp2') <- P.get f2

    let !src3' = A.append src1' src2'
        -- !(tmp'', src4') = merge tmp1' tmp2' src3'
    !(tmp'', src4') <- merge_par tmp1' tmp2' src3'
    pure (src4', tmp'')

msort'_par :: (Show a, Ord a) => A.Array a -> a -> P.Par (A.Array a)
msort'_par src anyVal = do
  let (len, src') = A.size2 src
      tmp = A.make len anyVal

  (src'', _tmp) <- msortInplace_par src' tmp

      -- src_copy = A.make len (A.get src 0)
      -- (_, src_copy') = A.copy2 src 0 src_copy 0 len
      -- (src'', _tmp) = msortInplace src_copy' tmp in
  pure (_tmp `seq` src'')

-- finally, the top-level merge sort function
{-# SPECIALISE msort_par :: A.Array Float -> P.Par (A.Array Float) #-}
{-# SPECIALISE msort_par :: A.Array Int -> P.Par (A.Array Int) #-}
msort_par :: (Show a, Ord a) => A.Array a -> P.Par (A.Array a)
msort_par src =
  let (len, src') = A.size2 src in
      if len == 0 then pure src'
      else do let (x0, src'') = A.get2 src' 0
              msort'_par src'' x0

goto_isort :: Int
goto_isort = 8192

goto_seqmerge :: Int
goto_seqmerge = 4196

merge_par :: (HasCallStack, Show a, Ord a) => A.Array a -> A.Array a -> A.Array a -> P.Par (A.Array a, A.Array a)
merge_par !src1 !src2 !dst =
    if A.size dst < goto_seqmerge
    then pure $ merge src1 src2 dst
    else let !(n1, src1') = A.size2 src1
             !(n2, src2') = A.size2 src2
             dst' = dst
             in if n1 == 0
                then do let !(src2'1, dst'') = A.copy2 src2' 0 dst' 0 n2
                        pure (A.append src1' src2'1, dst'')
                else if n2 == 0
                     then do let !(src1'1, dst'') = A.copy2 src1' 0 dst' 0 n1
                             pure (A.append src1'1 src2', dst'')
                     else
                       do let mid1 = n1 `div` 2
                              pivot = A.get src1' mid1
                              (mid2, src2'') = binarySearch src2' pivot

                              -- split src1
                              !(src1_l, src1_r) = A.splitAt mid1 src1'
                              !(src1_r1, src1_r2) = A.splitAt 1 src1_r

                              -- split src2
                              !(src2_l, src2_r) = A.splitAt mid2 src2''

                              -- set the pivot
                              !dst1 = A.set dst' (mid1+mid2) pivot

                              -- split dst
                              !(dst_l, dst_r) = A.splitAt (mid1+mid2) dst1
                              !(dst_r1, dst_r2) = A.splitAt 1 dst_r

                              -- sort the sub arrays
                          !(src_l, dst2) <- merge_par src1_l src2_l dst_l
                          !(src_r, dst3) <- merge_par src1_r2 src2_r dst_r2

                              -- append srcs and dsts
                          let src''' = A.append src_l (A.append src1_r1 src_r)
                              dst''' = A.append dst2 (A.append dst_r1 dst3)

                          pure (src''', dst''')



(.||.) :: a -> b -> (a,b)
a .||. b = a `par` b `pseq` (a,b)
  -- (a,b)

binarySearch :: Ord a => A.Array a -> a -> (Int, A.Array a)
binarySearch ls query = (go 0 (A.size ls), ls)
  where
    go lo hi = if n == 0
               then lo
               else if query < pivot
                    then go lo mid
                    else go (mid+1) hi
      where
        n = hi - lo
        mid = lo + n `div` 2
        pivot = A.get ls mid


--------------------------------------------------------------------------------

{- in place insertion sort; doesn't copy the input array -}
{-# INLINE isort2 #-}
{-# SPECIALISE isort2 :: A.Array Float -> A.Array Float #-}
isort2 :: Ord a => A.Array a -> A.Array a
isort2 xs = go 1 xs
  where
    !n = A.size xs
    go i ys =
      if i == n
      then ys
      else go (i+1) (shift i ys)

    -- shift j ys@(A.Arr ls s e) =
    shift !j ys =
      if j == 0
      -- then (A.Arr ls s e)
      then ys
      else let a = A.get ys j
               b = A.get ys (j-1)
           in if a > b
              -- then (A.Arr ls s e)
              then ys
              else let ys' = A.set (A.set ys j b) (j-1) a
                   in shift (j-1) ys'


--------------------------------------------------------------------------------

quickSort :: Ord a => A.Array a -> A.Array a
quickSort xs = quickSortBtw xs 0 (A.size xs)

quickSortBtw :: Ord a => A.Array a -> Int -> Int -> A.Array a
quickSortBtw xs i j  =
  if j - i < 2
  then xs
  else let (xs', i_piv) = shuffleBtw xs i j   -- isPartitionedBtw xs' i i_piv j
           xs''         = quickSortBtw xs'  i           i_piv
           xs'''        = quickSortBtw xs'' (i_piv + 1) j
        in xs'''

shuffleBtw :: Ord a => A.Array a -> Int -> Int -> (A.Array a, Int)
shuffleBtw xs i j =
  let
      (piv, xs1) = A.get2 xs (j-1)        -- fix xs[j-1] as the pivot
      -- at return, all of ws[i:ip] <= ws[j-1] and all of ws[ip:j-1] > ws[j-1].
      goShuffle zs jl jr    =   -- BOTH bounds inclusive here
        if jl > jr
        then (zs, jl)
        else let (vl, zs') = A.get2 zs jl in
          if vl <= piv
          then goShuffle zs' (jl+1) jr
          else let (vr, zs'') = A.get2 zs jr in
            if vr >  piv
            then goShuffle zs'' jl     (jr-1)
            else let zs''' = A.swap zs'' jl jr
                  in goShuffle zs''' jl (jr-1)

      (xs', ip)  = goShuffle xs1 i (j-2)  -- BOTH bounds inclusive
      xs''       = if ip < j-1
                   then A.swap xs' ip (j-1)
                   else xs'
   in (xs'', ip)
