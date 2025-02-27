module Merge where

import Gibbon.Vector

merge_ :: (a -> a -> Int) -> Vector a -> Vector a -> Int -> Int -> Vector a
merge_ cmp xs ys n m =
  if n == 0 then
    if m == 0 then generate (size xs + size ys) (\wild -> get xs 0)
    else let zs = merge_ cmp xs ys 0 (m-1) in set zs (m-1) (get ys (m-1))
  else
    if m == 0 then let zs = merge_ cmp xs ys (n-1) 0 in set zs (n-1) (get xs (n-1))
    else
      let
        xs_n = get xs (n-1)
        ys_m = get ys (m-1)
      in
        if cmp xs_n ys_m < 1 then
          let zs = merge_ cmp xs ys n (m-1)
           in set zs (m+n-1) ys_m
        else
          let zs = merge_ cmp xs ys (n-1) m
           in set zs (m+n-1) xs_n

msort_ :: (a -> a -> Int) -> Vector a -> Vector a
msort_ cmp xs =
  if size xs < 2 then xs
  else
    let
      (ls, rs) = splitMid xs
      ls' = msort_ cmp ls
      rs' = msort_ cmp rs
    in
      merge_ cmp ls' rs' (size ls') (size rs')
