module QSortHelper where

import Gibbon.Vector

get :: Vector Int -> Int -> Int
get v i = nth v i

set :: Vector Int -> Int -> Int -> Vector Int
set v i a = inplaceUpdate i a v

size :: Vector Int -> Int
size v = length v

size2 :: Vector Int -> (Int, Vector Int)
size2 ar = (size ar, ar)

get2 :: Vector Int -> Int -> (Int, Vector Int)
get2 ar i = (get ar i, ar)

swap :: Vector Int -> Int -> Int -> Vector Int
swap xs i j =
  let xi  = get xs i
      xs' = set xs i (get xs j)
      xs'' = set xs' j xi
  in xs''
