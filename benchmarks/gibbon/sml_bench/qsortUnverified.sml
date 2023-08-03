fun qsortInternal arr cmp = 
   let
     fun qsort(arr, lo, hi) = 
       if cmp lo hi < 0 then
         let
           val pivot = ArraySlice.sub(arr, hi)
           val i = ref (lo - 1)
           val j = ref lo
           val _ = 
             while cmp (!j) (hi - 1) < 1 do
               let
                 val _ = 
                   if cmp (ArraySlice.sub(arr, !j)) pivot < 0 then
                     let
                       val _ = i := !i + 1
                       val tmp = ArraySlice.sub(arr, !i)
                       val _ = ArraySlice.update(arr, !i, ArraySlice.sub(arr, !j))
                       val _ = ArraySlice.update(arr, !j, tmp)
                     in
                       ()
                     end
                   else ()
               in
                 j := !j + 1
               end
           val tmp = ArraySlice.sub(arr, !i + 1)
           val _ = ArraySlice.update(arr, !i + 1, ArraySlice.sub(arr, hi))
           val _ = ArraySlice.update(arr, hi, tmp)
           val p = !i + 1
           val _ = qsort(arr, lo, p - 1)
           val _ = qsort(arr, p + 1, hi)
         in
           ()
         end
     else ()
     val _ = qsort(arr, 0, ArraySlice.length arr - 1)
   in
     arr
   end
