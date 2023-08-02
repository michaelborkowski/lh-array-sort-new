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
    arr  end

fun generate_loop vec idx end_ f = 
  (if (idx = end_) then vec 
   else 
  let val vec1 = let val _ = (ArraySlice.update(vec , idx, (f idx))) in vec end in (generate_loop vec1 (idx + 1) end_ f) end)
and maxInt a b = 
  (if (a > b) then a 
   else b)
and generate n f = 
  let val n' = (maxInt n 0) in 
  let val vec = ((fn internal__ => ArraySlice.full(Array.array(internal__, 0))) n') in 
  let val vec1 = (generate_loop vec 0 n' f) in vec1 end end end
and nth vec i = (ArraySlice.sub(vec , i))
and copy vec = (generate (ArraySlice.length vec) (fn i => (nth vec i)))
and inplaceUpdate i val_ vec = let val _ = (ArraySlice.update(vec , i, val_)) in vec end
and shift j cmp ys = 
  (if (j = 0) then ys 
   else 
  let val a = (nth ys j) in 
  let val b = (nth ys (j - 1)) in 
  (if ((cmp a b) > 0) then ys 
   else 
  let val ys' = (inplaceUpdate j b ys) in 
  let val ys'' = (inplaceUpdate (j - 1) a ys') in (shift (j - 1) cmp ys'') end end) end end)
and go i n cmp ys = 
  (if (i = n) then ys 
   else 
  let val ys' = (shift i cmp ys) in (go (i + 1) n cmp ys') end)
and length vec = (ArraySlice.length vec)
and isort2 cmp xs = 
  let val n = (length xs) in (go 1 n cmp (copy xs)) end
and insert cmp xs x n = 
  (if (n = 0) then (inplaceUpdate 0 x xs) 
   else 
  let val y = (nth xs (n - 1)) in 
  (if ((cmp x y) < 0) then 
  let val xs' = (inplaceUpdate n y xs) in (insert cmp xs' x (n - 1)) end 
   else (inplaceUpdate n x xs)) end)
and isort cmp xs b n = 
  let val len = (length xs) in 
  (if (len <= 1) then xs 
   else 
  (if (n = 0) then b 
   else 
  let val xs' = (isort cmp xs b (n - 1)) in (insert cmp xs' (nth xs n) n) end)) end
and isort1 cmp xs = 
  let val n = (length xs) in 
  let val hd = (nth xs 0) in 
  let val b = (generate n (fn i => hd)) in (isort cmp xs b ((length xs) - 1)) end end end
and alloc vec = ((fn internal__ => ArraySlice.full(Array.array(internal__, 0))) vec)
and filter_loop idxs write_at start end_ from to = 
  (if (start = end_) then to 
   else 
  let val idx = (nth idxs start) in 
  (if (idx = (0 - 1)) then (filter_loop idxs write_at (start + 1) end_ from to) 
   else 
  let val elt = (nth from idx) in 
  let val to1 = let val _ = (ArraySlice.update(to , write_at, elt)) in to end in (filter_loop idxs (write_at + 1) (start + 1) end_ from to1) end end) end)
and foldl_loop idx end_ f acc vec = 
  (if (idx = end_) then acc 
   else 
  let val acc1 = (f acc (ArraySlice.sub(vec , idx))) in (foldl_loop (idx + 1) end_ f acc1 vec) end)
and foldl f acc vec = (foldl_loop 0 (ArraySlice.length vec) f acc vec)
and filter f vec = 
  let val idxs = (generate (ArraySlice.length vec) (fn i => 
  (if (f (nth vec i)) then i 
   else (0 - 1)))) in 
  let val num_ones = (foldl (fn acc => fn x => 
  (if (x = (0 - 1)) then acc 
   else (acc + 1))) 0 idxs) in 
  let val to = ((fn internal__ => ArraySlice.full(Array.array(internal__, 0))) num_ones) in 
  let val len_idxs = (ArraySlice.length idxs) in (filter_loop idxs 0 0 len_idxs vec to) end end end end
and cons x vec = 
  let val len = (ArraySlice.length vec) in 
  let val vec2 = ((fn internal__ => ArraySlice.full(Array.array(internal__, 0))) (len + 1)) in 
  let val vec3 = (generate_loop vec2 1 (len + 1) (fn i => (nth vec (i - 1)))) in 
  let val vec4 = let val _ = (ArraySlice.update(vec3 , 0, x)) in vec3 end in vec4 end end end end
and lcons x vec = 
  let val y = vec in (cons x y) end
and snoc vec x = 
  let val len = (ArraySlice.length vec) in 
  let val vec2 = ((fn internal__ => ArraySlice.full(Array.array(internal__, 0))) (len + 1)) in 
  let val vec3 = (generate_loop vec2 0 len (fn i => (nth vec i))) in 
  let val vec4 = let val _ = (ArraySlice.update(vec3 , len, x)) in vec3 end in vec4 end end end end
and lsnoc vec x = 
  let val y = vec in (snoc y x) end
and printVec_loop idx end_ vec f = 
  (if (idx = end_) then () 
   else 
  let val wildcard__187 = (f (ArraySlice.sub(vec , idx))) in 
  let val wildcard__184 = (print ",") in (printVec_loop (idx + 1) end_ vec f) end end)
and printVec f vec = 
  let val wildcard__178 = (print "[") in 
  let val wildcard__176 = (printVec_loop 0 (ArraySlice.length vec) vec f) in 
  let val wildcard__173 = (print "]") in () end end end
and ifoldl_loop idx end_ f acc vec = 
  (if (idx = end_) then acc 
   else 
  let val acc1 = (f acc idx (ArraySlice.sub(vec , idx))) in (ifoldl_loop (idx + 1) end_ f acc1 vec) end)
and ifoldl f acc vec = (ifoldl_loop 0 (ArraySlice.length vec) f acc vec)
and lifoldl f acc vec = 
  let val x = vec in (ifoldl f acc x) end
and scanl_loop idx end_ f acc vec result = 
  (if (idx = end_) then result 
   else 
  let val acc1 = (f acc (ArraySlice.sub(vec , idx))) in 
  let val result' = let val _ = (ArraySlice.update(result , idx, acc1)) in result end in (scanl_loop (idx + 1) end_ f acc1 vec result') end end)
and scanl f acc vec = 
  let val len = (ArraySlice.length vec) in 
  let val result = ((fn internal__ => ArraySlice.full(Array.array(internal__, 0))) len) in (scanl_loop 0 len f acc vec result) end end
and lscanl f acc vec = 
  let val x = vec in (scanl f acc x) end
and lfoldl f acc vec = 
  let val x = vec in (foldl f acc x) end
and update vec i x = (generate (length vec) (fn j => 
  (if (i = j) then x 
   else (ArraySlice.sub(vec , j)))))
and map f vec = (generate (ArraySlice.length vec) (fn i => (f (ArraySlice.sub(vec , i)))))
and lmap f vec = 
  let val x = vec in (map f x) end
and select v1 v2 i = 
  let val len = (ArraySlice.length v1) in 
  (if (i < len) then (ArraySlice.sub(v1 , i)) 
   else (ArraySlice.sub(v2 , (i - len)))) end
and append v1 v2 = (generate ((ArraySlice.length v1) + (ArraySlice.length v2)) (fn i => (select v1 v2 i)))
and lcopy vec = (copy vec)
and slice i n vec = ArraySlice.subslice(vec , i, (SOME n))
and tail vec = (slice 1 ((ArraySlice.length vec) - 1) vec)
and head vec = (nth vec 0)
and minInt a b = 
  (if (a < b) then a 
   else b)
and splitAt n vec = 
  let val len = (ArraySlice.length vec) in 
  let val n' = (maxInt n 0) in 
  let val m = (minInt n' len) in 
  let val m' = (maxInt 0 (len - n')) in (ArraySlice.subslice(vec , 0, (SOME m)) ,  ArraySlice.subslice(vec , m, (SOME m'))) end end end end
and lsplitAt' n vec = 
  let val tup_74 = (splitAt n vec) in 
  let val x = (case tup_74 of (x__, _) => x__) in 
  let val y = (case tup_74 of (_, x__) => x__) in ((ArraySlice.length x) ,  x,  (ArraySlice.length y),  y) end end end
and lsplitAt n vec = 
  let val x = vec in (lsplitAt' n x) end
and singleton x = 
  let val vec = ((fn internal__ => ArraySlice.full(Array.array(internal__, 0))) 1) in 
  let val vec2 = let val _ = (ArraySlice.update(vec , 0, x)) in vec end in vec2 end end
and isEmpty vec = ((ArraySlice.length vec) = 0)
and inplaceSort cmp vec = (qsortInternal vec cmp)
and flatten ls = raise (Fail "VConcatP")
and sort cmp vec = raise (Fail "VSortP")
and merge vec1 vec2 = raise (Fail "VMergeP")
and unsafeSlice i n vec = ArraySlice.subslice(vec , i, (SOME n))
and nth2 vec i = 
  let val tup_26 = vec in 
  let val vec1 = tup_26 in 
  let val vec2 = tup_26 in ((ArraySlice.sub(vec1 , i)) ,  vec2) end end end
and nth1 vec i = (ArraySlice.sub(vec , i))
and length2 vec = 
  let val tup_12 = vec in 
  let val vec1 = tup_12 in 
  let val vec2 = tup_12 in ((ArraySlice.length vec1) ,  vec2) end end end
and length1 vec = (ArraySlice.length vec)
and print_space wildcard__20 = print " "
and print_newline wildcard__18 = print "\n"
and print_check b = ()
and compare_int r1 r2 = 
  (if (r1 < r2) then (0 - 1) 
   else 
  (if (r1 > r2) then 1 
   else 0))
and compare_float r1 r2 = 
  (if (r1 < r2) then (0 - 1) 
   else 
  (if (r1 > r2) then 1 
   else 0))
and float_abs f = 
  (if (f < 0.0) then (f * (0.0 - 1.0)) 
   else f)
and minFloat a b = 
  (if (a < b) then a 
   else b)
and maxFloat a b = 
  (if (a > b) then a 
   else b);

