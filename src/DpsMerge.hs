{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--no-termination"  @-}
{-@ LIQUID "--no-totality"  @-}

module DpsMerge where

import qualified Language.Haskell.Liquid.Bag as B
import           Language.Haskell.Liquid.ProofCombinators
import qualified Array as A
import           Equivalence
--import Debug.Trace


-- Helper functions
                -- ((A.size (fst t)) = (mydiv (A.size xs)))} @-}
                -- A.size (fst t) < (A.size xs) && 
                -- A.size (snd t) < (A.size xs) && 
{- @ reflect splitMid @-}
{-@ splitMid :: xs:{A.size xs >= 2} 
      -> {t:_ | toBag xs == B.union (toBag (fst t)) (toBag (snd t)) &&
                token (fst t) == token xs && token (snd t) == token xs &&
                right (fst t) == left (snd t) &&
                right (fst t) == left xs + div (size xs) 2 &&
                left (fst t) == left xs && right (snd t) == right xs &&
                A.size (fst t) == div (size xs) 2 &&
                A.size (snd t) == A.size xs - div (size xs) 2 &&
                A.size xs = (A.size (fst t)) + (A.size (snd t)) } @-}
splitMid :: A.Array a -> (A.Array a, A.Array a)
splitMid xs = (A.slice xs 0 m, A.slice xs m n)
  where
    n = A.size xs
    m = n `div` 2

-- copy sets dst[j..] <- src[i..]
{-@ copy :: src:(Array a) -> { dst:(Array a) | size dst >= size src }
         -> { i:Nat | i >= 0 && i <= size src }
         -> { j:Nat | j >= 0 && j <= size dst && (size dst) - j == (size src) - i }
         -> { t:_ | toBagBtw src i (size src) == toBagBtw (snd t) j (size dst) &&
                    token (fst t) == token src && token (snd t) == token dst && 
                    left (fst t) == left src && right (fst t) == right src &&
                    left (snd t) == left dst && right (snd t) == right dst &&
                    A.size (fst t) == A.size src &&
                    A.size (snd t) == A.size dst } @-}
copy :: A.Array a -> A.Array a -> Int -> Int -> (A.Array a, A.Array a)
copy src dst i j =
  let (len, src') = A.size2 src in
  if i < len
  then
    let (v, src'1) = A.get2 src' i in
    copy src'1 (A.set dst j v) 
               (i + 1) (j + 1)
  else (src', dst)

-- DPS merge
{-@ merge' :: xs1:(Array a)
         -> { xs2:(Array a) | token xs1 == token xs2 && right xs1 == left xs2 }
         -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
         -> { i1:Nat | i1 <= size xs1 } -> { i2:Nat | i2 <= size xs2 }   
         -> { j:Nat  | i1 + i2 == j && j <= size zs &&
                       B.union (toBagBtw xs1 0 i1) (toBagBtw xs2 0 i2) == toBagBtw zs 0 j }
         -> { t:_           | B.union (toBag xs1) (toBag xs2) == toBag zs &&
                              left (fst t) == left xs1 && right (fst t) == right xs2 &&
                              left (snd t) == left zs  && right (snd t) == right zs  &&
                              size (fst t) == size xs1 + size xs2 && size (snd t) == size zs &&
                              token xs1 == token (fst t) && token xs2 == token (fst t) && 
                              token zs  == token (snd t) } @-}
merge' :: Ord a =>
  A.Array a -> A.Array a -> A.Array a ->
  Int -> Int -> Int ->
  (A.Array a, A.Array a)
merge' src1 src2 dst i1 i2 j =
  let (len1, src1') = A.size2 src1
      (len2, src2') = A.size2 src2 in
  if i1 >= len1
  then
    let (src2'1, dst') = copy src2' dst i2 j in (A.append src1' src2'1, dst')
  else if i2 >= len2
  then
    let (src1'1, dst') = copy src1' dst i1 j in (A.append src1'1 src2', dst')
  else
    let (v1, src1'1) = A.get2 src1' i1
        (v2, src2'1) = A.get2 src2' i2 in
    if v1 < v2
    then merge' src1'1 src2'1 (A.set dst j v1) (i1 + 1) i2 (j + 1)
    else merge' src1'1 src2'1 (A.set dst j v2) i1 (i2 + 1) (j + 1)

    -- Possible: (right xs1 == left xs2) => (left xs1 == left (fst t) && right xs2 == right (fst t))
{-@ merge :: xs1:(Array a)
        -> { xs2:(Array a) | token xs1 == token xs2 && right xs1 == left xs2 }
        -> {  zs:(Array a) | size xs1 + size xs2 == size zs }
        -> { t:_           | B.union (toBag xs1) (toBag xs2) == toBag (snd t) &&
                             left (fst t) == left xs1 && right (fst t) == right xs2 &&
                             left (snd t) == left zs  && right (snd t) == right zs  &&
                             size (fst t) == size xs1 + size xs2 && size (snd t) == size zs &&
                             token xs1 == token (fst t) && token xs2 == token (fst t) &&
                             token zs  == token (snd t) } @-}
merge :: Ord a => A.Array a -> A.Array a -> A.Array a -> (A.Array a, A.Array a)
merge src1 src2 dst = merge' src1 src2 dst 0 0 0   -- the 0's are relative to the current
                                                   --   slices, not 

-- DPS mergesort
--                      not (token xs == token ys) && right xs == right ys }
{-@ msortSwap :: xs:Array a 
      -> { ys:(Array a ) | A.size ys  == A.size xs   && left xs == left ys && 
                           right xs == right ys }
      -> (Array a, Array a)<{\zs ts -> A.size xs == A.size ts && A.size ys == A.size zs &&
                                       token xs == token ts && token ys == token zs &&
                                       toBag xs == toBag ts &&
                                       left ts == left xs && right ts == right xs &&
                                       left zs == left ys && right zs == right ys }> 
       / [A.size xs] @-}
msortSwap :: (Show a, Ord a) => A.Array a -> A.Array a -> (A.Array a, A.Array a)
msortSwap src tmp =
  let (len, src') = A.size2 src in
  if len <= 1
  then (tmp, src')
  else
    let (src1, src2) = splitMid src'
        (tmp1, tmp2) = splitMid tmp
        (src1', tmp1') = msortInplace src1 tmp1
        (src2', tmp2') = msortInplace src2 tmp2
        tmp3' = A.append tmp1' tmp2' 
        (src'', tmp4) = merge src1' src2' tmp3'
    in (tmp4, src'') -- tmp4 holds the sorted data

--                      not (token xs == token ys) && right xs == right ys }
{-@ msortInplace :: xs:Array a 
      -> { ys:(Array a ) | A.size ys  == A.size xs   && left xs == left ys && 
                      right xs == right ys }
      -> (Array a, Array a)<{\zs ts -> A.size xs == A.size zs && A.size ys == A.size ts &&
                                       token xs == token zs && token ys == token ts &&
                                       toBag xs == toBag zs &&
                                       left zs == left xs && right zs == right xs &&
                                       left ts == left ys && right ts == right ys }> 
       / [A.size xs] @-}
msortInplace :: (Show a, Ord a) => A.Array a -> A.Array a -> (A.Array a, A.Array a)
msortInplace src tmp =
  let (len, src') = A.size2 src in
  if len <= 1
  then (src', tmp)
  else
    let (src1, src2) = splitMid src'
        (tmp1, tmp2) = splitMid tmp
        (tmp1', src1') = msortSwap{-Inplace-} src1 tmp1
        (tmp2', src2') = msortSwap{-Inplace-} src2 tmp2
        src3'{-tmp3'-} = A.append src1' src2' {-tmp1' tmp2'-} 
        (tmp''{-_src''-}, src4'{-tmp4-}) = merge tmp1' tmp2' src3' {-src1' src2' tmp3'-}
    in (src4'{-tmp4-}, tmp''{-_src''-})  -- src4' holds the sorted data

{-@ msort' :: { xs:(Array a) | A.size xs > 0 && left xs == 0 && right xs == size xs }
           -> { y:a | y == A.get xs 0 }
           -> { zs:(Array a) | A.size xs == A.size zs && token xs == token zs &&
                               toBag xs == toBag zs } @-}
msort' :: (Show a, Ord a) => A.Array a -> a -> A.Array a
msort' src anyVal =
  let (len, src') = A.size2 src
      (src'', _tmp) = msortInplace src' (A.make len anyVal) in
  _tmp `seq` src''

-- finally, the top-level merge sort function -- TODO: use A.get2/A.size2 for linearity
{-@ msort :: { xs:(A.Array a) | left xs == 0 && right xs == size xs }
           -> { ys:(A.Array a) | A.size xs == A.size ys && token xs == token ys && 
                                 toBag xs == toBag ys } @-}
msort :: (Show a, Ord a) => A.Array a -> A.Array a
msort src =
  let (len, src') = A.size2 src in
      if len == 0 then src'
      else let (x0, src'') = A.get2 src' 0 in msort' src'' x0






{- CODE SECTION NOT IN USE YET

goto_seqmerge :: Int
goto_seqmerge = 4

merge_par :: (Show a, Ord a) => A.Array a -> A.Array a -> A.Array a -> A.Array a
merge_par src1 src2 dst =
    if A.size dst < goto_seqmerge
    then let (_src', dst') = merge src1 src2 dst
         in dst'
    else let n1 = A.size src1
             n2 = A.size src2
             n3 = A.size dst
             in if n1 == 0
                then let (_src2', dst') = copy src2 dst 0 0
                     in dst'
                else if n2 == 0
                     then let (_src1', dst') = copy src1 dst 0 0
                          in dst'
                     else let mid1 = n1 `div` 2
                              pivot = A.get src1 mid1
                              mid2 = binarySearch src2 pivot
                              src1_l = slice2 0 mid1 src1
                              src1_r = slice2 (mid1+1) (n1 - (mid1+1)) src1
                              src2_l = slice2 0 mid2 src2
                              src2_r = slice2 mid2 (n2-mid2) src2
                              dst1 = A.set dst (mid1+mid2) pivot
                          {-
                              -- Need a true slice of dst; writes to one slice
                              -- should reflect in the other after they're merged.
                              -- The slices backed by lists don't work here since
                              -- each slice is backed by it's own list...
                              --
                              -- Maybe we can make A.append do this work.
                              dst_l = slice2 0 (mid1+mid2) dst1
                              dst_r = slice2 (mid1+mid2+1) (n3 - (mid1+mid2+1)) dst1
                              dst2 = merge_par src1_l src2_l dst_l
                              dst3 = merge_par src1_r src2_r dst_r
                          -}
                              dst_l = slice2 0 (mid1+mid2) dst1
                              (A.Arr _ lo1 hi1) = slice2 (mid1+mid2+1) (n3 - (mid1+mid2+1)) dst1
                              (A.Arr ls2 lo2 _hi2) = merge_par src1_l src2_l dst_l
                              (A.Arr ls3 _lo3 hi3) = merge_par src1_r src2_r (A.Arr ls2 lo1 hi1)
                          in A.Arr ls3 lo2 hi3
  where
    slice2 :: Int -- starting index
           -> Int -- length of slice
           -> A.Array a
           -> A.Array a
    slice2 i n (A.Arr ls l r) =
        let l' = l + i
            r' = l + i + n
        in if l' > r || r' > r
        then error $ "slice2: out of bound, in=" ++ show (l,r) ++ ", slice=" ++ show (l',r')
        else A.Arr ls l' r'

binarySearch :: Ord a => A.Array a -> a -> Int
binarySearch ls query = go 0 (A.size ls)
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

END UNUSED SECTION -}

