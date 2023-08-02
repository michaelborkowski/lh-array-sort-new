module QuickSort where

import Gibbon.Vector

quickSort :: Vector Int -> Vector Int
quickSort xs cmp =
  let (len, xs1) = size2 xs
      (hd, xs2) = get2 xs1 0
      cpy = alloc len hd (\tmp -> copy xs2 0 tmp 0 len)
  in quickSortBtw cpy 0 len

quickSortBtw :: Vector Int -> Int -> Int -> Vector Int
quickSortBtw xs i j  =
  if j - i < 2
  then xs
  else let (xs', i_piv) = shuffleBtw xs i j
           xs''         = quickSortBtw xs'  i           i_piv
           xs'''        = quickSortBtw xs'' (i_piv + 1) j
        in xs'''

shuffleBtw :: Vector Int -> Int -> Int -> (Vector Int, Int)
shuffleBtw xs i j =
  let
      (piv, xs1) = get2 xs (j-1)
      goShuffle zs jl jr = 
        if jl > jr
        then (zs, jl)
        else let (vl, zs') = get2 zs jl in
          if vl <= piv
          then goShuffle zs' (jl+1)
                             jr
          else let (vr, zs'') = get2 zs' jr in
            if vr >  piv
            then goShuffle zs'' jl     (jr-1)
            else let zs''' = swap zs'' jl jr
                  in goShuffle zs''' jl (jr-1)

      (xs', ip)  = goShuffle xs1 i (j-2)  -- BOTH bounds inclusive
      xs''       = if ip < j-1
                   then swap xs' ip (j-1)
                   else xs'
   in (xs'', ip)
