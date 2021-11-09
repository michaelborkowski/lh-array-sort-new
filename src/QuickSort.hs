{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ LIQUID "--short-names" @-}

module QuickSort where

import Language.Haskell.Liquid.ProofCombinators
import Array
import Equivalence
import Order

{-@ quickSort :: xs:(Array a) -> { zs:(Array a) | size xs == size zs }
                              -> { ys:(Array a) | isSorted ys && toBag xs == toBag ys } @-}
quickSort :: Ord a => Array a -> Array a -> Array a
-- quickSort xs zs = quickSortBtw xs zs 0 (size xs)
quickSort xs zs = if size xs < 2
                    then zs
                    else let (zs', i_piv)  = shuffle xs zs 
                             (zls', zrest) = splitAt zs' i_piv
                             (xls,  xrest) = splitAt xs  i_piv 
                             (_, zrs')     = splitAt zls' 1 
                             (_, xrs)      = splitAt xls  1 
                             xls'          = quickSort zls' xls 
                             xrs'          = quickSort zrs' xrs 
                             zs''          = copyWithPivot xls' (get zs' i_piv) xrs' zs'
                          in zs'' ? lem_sorted_partitions zs'' i_piv

{-@ copyWithPivot :: xls:(Array a) -> piv:a -> xrs:(Array a) 
                                   -> { zs:(Array a) | size zs == size xls + 1 + size xrs }
                                   -> { ys:(Array a) | size ys == size xls + 1 + size xrs &&
                                                       toBag ys == Map_union (toBag xls)
                                                                     (Map_union (toBag xrs)
                                                                        (Map_store piv 1 empty) } @-}
copyWithPivot :: Ord a => Array a -> a -> Array a -> Array a -> Array a
copyWithPivot xls piv xrs zs = undefined

-- xs ranges from 0..i_piv+1
-- 0 <= i < i_piv  and  0 <= jl < jr <= i_piv
{-@ shuffle :: xs:(Array a) -> { zs:(Array a) | size xs == size zs }
                  -> (Array a, Int)<{\ys ip -> isPartitioned ys ip && toBag xs == toBag ys
                                               0 <= ip && ip < size ys }> @-}
shuffle :: Ord a => Array a -> Array a -> (Vec a, Int)
shuffle xs zs = goShuffle xs 0 zs 0 ((size zs) - 1)

{-@ goShuffle :: xs:(Array a) -> { i:Int | 0 <= i && i < size xs } 
                    -> { zs:(Array a) | size xs == size zs }
                    -> { jl:Int | 0 <= jl }
                    -> { jr:Int | jl <= jr && jr < size zs && 
                                  rangeUpperBound zs 0      jl        (get xs ((size xs) - 1)) &&
                                  rangeLowerBound zs (jr+1) (size zs) (get xs ((size xs) - 1)) &&
                                  toBagBtw xs 0 i == Map_union (toBagBtw zs 0 jl) 
                                                               (toBagBtw zs (jr+1) (size zs)) }  
                    -> (Array a, Int)<{\ys ip -> isPartitioned ys ip && toBag xs == toBag ys
                                               0 <= ip && ip < size ys }> @-}
goShuffle :: Ord a => Array a -> Int -> Array a -> Int -> Int -> (Array a, Int)
goShuffle xs i zs jl jr 
    | jl >= jr         = (set zs jl pivot, jl)
    | get xs i < pivot = let zs' = set zs jl (get xs i)
                          in goShuffle xs (i+1) zs' (jl+1) jr
    | otherwise        = let zs' = set zs jr (get xs i)
                          in goShuffle xs (i+1) zs' jl (jr-1)
  where
    pivot = get xs ((size xs) - 1)


{-@ reflect isPartitioned @-}
{-@ isPartitioned :: xs:(Array a) -> { i_piv:Int | 0 <= i_piv && i_piv < size xs } -> Bool @-}
isPartitioned :: Ord a => Array a -> Int -> Bool
isPartitioned xs i_piv = rangeUpperBound xs n0          i_piv     (get xs i_piv) &&
                         rangeLowerBound xs (i_piv + 1) (size xs) (get xs i_piv)
                         -- isPartitionedBtw xs i_piv 0 ((size xs)-1)

{-@ reflect rangeUpperBound @-}
{-@ rangeUpperBound :: xs:(Array a) -> { n0:Int | 0 <= n0 } -> { n1:Int | n0 <=n1 && n1 <= size xs }
                                    -> a -> Bool @-}
rangeUpperBound :: Ord a => Array a -> Int -> Int -> a -> Bool
rangeUpperBound xs n0 n1 v | n0 >= n1  = True
                           | otherwise = (get xs n0 < v)  && rangeUpperBound xs (n0+1) n1 v

{-@ reflect rangeLowerBound @-}
{-@ rangeLowerBound :: xs:(Array a) -> { n0:Int | 0 <= n0 } -> { n1:Int | n0 <=n1 && n1 <= size xs }
                                    -> a -> Bool @-}
rangeLowerBound :: Ord a => Array a -> Int -> Int -> a -> Bool
rangeLowerBound xs n0 n1 v | n0 >= n1  = True
                           | otherwise = (v <= get xs n0) && rangeLowerBound xs (n0+1) n1 v

{-@ lem_sorted_partitions @-}
{-@ lem_sorted_partitions :: xs:(Array a) -> { i_piv:Int | 0 <= i_piv && i_piv < size xs &&
                                                           isSortedBtw xs 0 i_piv &&
                                                           isSortedBtw xs (i_piv+1) (size xs) &&
                                                           isPartitioned xs i_piv } 
                                          -> { pf:_ | isSorted xs } @-}                            
lem_sorted_partitions :: Ord a => Array a -> Int -> Proof
lem_sorted_partitions = undefined


 --------------------
 --- currently unused

{- @ reflect isPartitionedBtwIncl @-}
{- @ isPartitionedBtwIncl :: xs:(Array a) -> { i_piv:Int | 0 <= i_piv && i_piv < size xs }
                               -> { n0:Int | 0 <= n0 && n0 <= i_piv }
                               -> { n1:Int | i_piv <= n1 && n1 < size xs } -> Bool @-}
isPartitionedBtwIncl :: Ord a => Array a -> Int -> Int -> Int -> Bool
isPartitionedBtwIncl xs i_piv n0 n1
  | n0 == i_piv && i_piv == n1  = True
  | n0 == i_piv                 = (get xs i_piv < get xs n1)  && isPartitionedBtwIncl xs i_piv n0 (n1-1)
  | otherwise                   = (get xs n0 <= get xs i_piv) && isPartitionedBtwIncl xs i_piv (n0+1) n1

