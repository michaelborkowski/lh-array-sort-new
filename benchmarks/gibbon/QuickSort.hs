module QuickSort where

import Gibbon.Vector

quickSort :: Vector Int -> (Int -> Int -> Int) -> Vector Int
quickSort xs cmp =
  let len = size xs
  in quickSortBtw (copy xs) cmp 0 len

quickSortBtw :: Vector Int -> (Int -> Int -> Int) -> Int -> Int -> Vector Int
quickSortBtw xs cmp i j  =
  if j - i < 2
  then xs
  else let (xs', i_piv) = shuffleBtw xs cmp i j
           xs''         = quickSortBtw xs' cmp  i           i_piv
           xs'''        = quickSortBtw xs'' cmp (i_piv + 1) j
        in xs'''

shuffleBtw :: Vector Int -> (Int -> Int -> Int) -> Int -> Int -> (Vector Int, Int)
shuffleBtw xs cmp i j =
  let
      (piv, xs1) = get2 xs (j-1)
      goShuffle zs jl jr =
        if jl > jr
        then (zs, jl)
        else let (vl, zs') = get2 zs jl in
          if cmp vl piv < 1
          then goShuffle zs' (jl+1)
                             jr
          else let (vr, zs'') = get2 zs' jr in
            if cmp vr piv > 0
            then goShuffle zs'' jl     (jr-1)
            else let zs''' = swap zs'' jl jr
                  in goShuffle zs''' jl (jr-1)

      (xs', ip)  = goShuffle xs1 i (j-2)  -- BOTH bounds inclusive
      xs''       = if ip < j-1
                   then swap xs' ip (j-1)
                   else xs'
   in (xs'', ip)
