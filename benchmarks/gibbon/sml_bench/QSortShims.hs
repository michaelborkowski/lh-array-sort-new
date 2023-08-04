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

copy2 :: Vector a -> Int -> Vector a -> Int -> Int -> (Vector a, Vector a)
copy2 a _ b _ _ = 
  let
    c = copy b
    len = length c
    aux i = 
      if i < len then
        let
          _ = set c i (get a i)
        in
          aux (i + 1)
      else ()
    _ = aux 0
  in
  (a, c)

swap :: Vector Int -> Int -> Int -> Vector Int
swap xs i j = 
  let xi  = get xs i
      xs' = set xs i (get xs j)
      xs'' = set xs' j xi
  in xs''

splitMid :: Vector a -> (Vector a, Vector a)
splitMid v0 = splitAt (length v0 / 2) v0
