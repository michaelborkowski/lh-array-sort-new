
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
and select v1 v2 i = 
  let val len = (ArraySlice.length v1) in 
  (if (i < len) then (ArraySlice.sub(v1 , i)) 
   else (ArraySlice.sub(v2 , (i - len)))) end
and append v1 v2 = (generate ((ArraySlice.length v1) + (ArraySlice.length v2)) (fn i => (select v1 v2 i)))
and msortInplace cmp src tmp = 
  let val tup_56 = (size2 src) in 
  let val len = (case tup_56 of (x__, _) => x__) in 
  let val src' = (case tup_56 of (_, x__) => x__) in 
  (if (len <= 1) then (src' ,  tmp) 
   else 
  let val tup_52 = (splitMid src') in 
  let val src1 = (case tup_52 of (x__, _) => x__) in 
  let val src2 = (case tup_52 of (_, x__) => x__) in 
  let val tup_48 = (splitMid tmp) in 
  let val tmp1 = (case tup_48 of (x__, _) => x__) in 
  let val tmp2 = (case tup_48 of (_, x__) => x__) in 
  let val tup_44 = (msortSwap cmp src1 tmp1) in 
  let val src1' = (case tup_44 of (x__, _) => x__) in 
  let val tmp1' = (case tup_44 of (_, x__) => x__) in 
  let val tup_40 = (msortSwap cmp src2 tmp2) in 
  let val src2' = (case tup_40 of (x__, _) => x__) in 
  let val tmp2' = (case tup_40 of (_, x__) => x__) in 
  let val src3' = (append src1' src2') in 
  let val tup_35 = (mergeVerified cmp tmp1' tmp2' src3') in 
  let val tmp'' = (case tup_35 of (x__, _) => x__) in 
  let val src4' = (case tup_35 of (_, x__) => x__) in (src4' ,  tmp'') end end end end end end end end end end end end end end end end) end end end
and msortSwap cmp src tmp = 
  let val tup_28 = (size2 src) in 
  let val len = (case tup_28 of (x__, _) => x__) in 
  let val src' = (case tup_28 of (_, x__) => x__) in 
  (if (len <= 1) then 
  let val tup_3 = (copy2 src' 0 tmp 0 len) in 
  let val src'' = (case tup_3 of (x__, _) => x__) in 
  let val tmp'' = (case tup_3 of (_, x__) => x__) in (src'' ,  tmp'') end end end 
   else 
  let val tup_24 = (splitMid src') in 
  let val src1 = (case tup_24 of (x__, _) => x__) in 
  let val src2 = (case tup_24 of (_, x__) => x__) in 
  let val tup_20 = (splitMid tmp) in 
  let val tmp1 = (case tup_20 of (x__, _) => x__) in 
  let val tmp2 = (case tup_20 of (_, x__) => x__) in 
  let val tup_16 = (msortInplace cmp src1 tmp1) in 
  let val src1' = (case tup_16 of (x__, _) => x__) in 
  let val tmp1' = (case tup_16 of (_, x__) => x__) in 
  let val tup_12 = (msortInplace cmp src2 tmp2) in 
  let val src2' = (case tup_12 of (x__, _) => x__) in 
  let val tmp2' = (case tup_12 of (_, x__) => x__) in 
  let val tmp3' = (append tmp1' tmp2') in 
  let val tup_7 = (mergeVerified cmp src1' src2' tmp3') in 
  let val src'' = (case tup_7 of (x__, _) => x__) in 
  let val tmp4 = (case tup_7 of (_, x__) => x__) in (src'' ,  tmp4) end end end end end end end end end end end end end end end end) end end end
and nth vec i = (ArraySlice.sub(vec , i))
and copy vec = (generate (ArraySlice.length vec) (fn i => (nth vec i)))
and msort' cmp src anyVal = 
  let val tup_67 = (size2 src) in 
  let val len = (case tup_67 of (x__, _) => x__) in 
  let val src1 = (case tup_67 of (_, x__) => x__) in 
  let val tup_64 = (msortInplace cmp src1 (copy src1)) in 
  let val a = (case tup_64 of (x__, _) => x__) in 
  let val src2 = (copy a) in src2 end end end end end end
and msort cmp src = 
  let val tup_78 = (size2 src) in 
  let val len = (case tup_78 of (x__, _) => x__) in 
  let val src1 = (case tup_78 of (_, x__) => x__) in 
  (if (len = 0) then src1 
   else 
  let val tup_74 = (get2 src1 0) in 
  let val x0 = (case tup_74 of (x__, _) => x__) in 
  let val src2 = (case tup_74 of (_, x__) => x__) in 
  let val cpy2 = (copy src2) in (msort' cmp cpy2 x0) end end end end) end end end
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
and length vec = (ArraySlice.length vec)
and update vec i x = (generate (length vec) (fn j => 
  (if (i = j) then x 
   else (ArraySlice.sub(vec , j)))))
and map f vec = (generate (ArraySlice.length vec) (fn i => (f (ArraySlice.sub(vec , i)))))
and lmap f vec = 
  let val x = vec in (map f x) end
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
and inplaceUpdate i val_ vec = let val _ = (ArraySlice.update(vec , i, val_)) in vec end
and inplaceSort cmp vec = (quickSort vec cmp)
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

