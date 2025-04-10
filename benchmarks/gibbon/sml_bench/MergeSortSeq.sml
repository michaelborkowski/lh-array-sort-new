val goto_seqmerge = 4096;
fun ifoldl_loop idx end_ f acc vec =
  (if (idx = end_) then acc
   else
  let val acc1 = (f acc idx (ArraySlice.sub(vec , idx))) in (ifoldl_loop (idx + 1) end_ f acc1 vec) end)
and ifoldl f acc vec = (ifoldl_loop 0 (ArraySlice.length vec) f acc vec)
and length vec = (ArraySlice.length vec)
and nth vec i = (ArraySlice.sub(vec , i))
and print_check b = ()
and slice i n vec = ArraySlice.subslice(vec , i, (SOME n))
and check_sorted cmp sorted =
  let val len = (length sorted) in
  (if (len <= 1) then (print_check true)
   else
  let val arr1 = (slice 0 (len - 2) sorted) in
  let val check = (ifoldl (fn acc => fn i => fn elt1 =>
  let val elt2 = (nth arr1 (i + 1)) in (acc andalso ((cmp elt1 elt2) <= 0)) end) true arr1) in (print_check check) end end) end
and generate_loop vec idx end_ f =
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
and copy vec = (generate (ArraySlice.length vec) (fn i => (nth vec i)));
val gotoQuickSort = 8192;
fun inplaceSort cmp vec = (quickSort vec cmp)
and minInt a b =
  (if (a < b) then a
   else b)
and splitAt n vec =
  let val len = (ArraySlice.length vec) in
  let val n' = (maxInt n 0) in
  let val m = (minInt n' len) in
  let val m' = (maxInt 0 (len - n')) in (ArraySlice.subslice(vec , 0, (SOME m)) ,  ArraySlice.subslice(vec , m, (SOME m'))) end end end end
and inplaceUpdate i val_ vec = let val _ = (ArraySlice.update(vec , i, val_)) in vec end
and write_loop_seq to_idx from_idx end_ from to =
  (if (from_idx = end_) then to
   else
  let val to1 = (inplaceUpdate to_idx (nth from from_idx) to) in (write_loop_seq (to_idx + 1) (from_idx + 1) end_ from to1) end)
and writeMerge_seq_loop i1 i2 j n1 n2 cmp src_1 src_2 tmp =
  (if (i1 = n1) then
  let val tmp_2 = (write_loop_seq j i2 n2 src_2 tmp) in tmp_2 end
   else
  (if (i2 = n2) then
  let val tmp_2 = (write_loop_seq j i1 n1 src_1 tmp) in tmp_2 end
   else
  let val x1 = (nth src_1 i1) in
  let val x2 = (nth src_2 i2) in
  (if ((cmp x1 x2) < 0) then
  let val tmp_1 = (inplaceUpdate j x1 tmp) in (writeMerge_seq_loop (i1 + 1) i2 (j + 1) n1 n2 cmp src_1 src_2 tmp_1) end
   else
  let val tmp_1 = (inplaceUpdate j x2 tmp) in (writeMerge_seq_loop i1 (i2 + 1) (j + 1) n1 n2 cmp src_1 src_2 tmp_1) end) end end))
and writeMerge_seq cmp src_1 src_2 tmp =
  let val n1 = (length src_1) in
  let val n2 = (length src_2) in
  let val res = (writeMerge_seq_loop 0 0 0 n1 n2 cmp src_1 src_2 tmp) in res end end end
and writeSort2_seq cmp src tmp =
  let val len = (length src) in
  (if (len < (gotoQuickSort)) then
  let val tmp_1 = (write_loop_seq 0 0 len src tmp) in (inplaceSort cmp tmp_1) end
   else
  let val half = (len div 2) in
  let val tup_73 = (splitAt half src) in
  let val src_l = (case tup_73 of (x__, _) => x__) in
  let val src_r = (case tup_73 of (_, x__) => x__) in
  let val tup_69 = (splitAt half tmp) in
  let val tmp_l = (case tup_69 of (x__, _) => x__) in
  let val tmp_r = (case tup_69 of (_, x__) => x__) in
  let val src_l1 = (writeSort1_seq cmp src_l tmp_l) in
  let val src_r1 = (writeSort1_seq cmp src_r tmp_r) in
  let val res = (writeMerge_seq cmp src_l1 src_r1 tmp) in res end end end end end end end end end end) end
and writeSort1_seq cmp src tmp =
  let val len = (length src) in
  (if (len < (gotoQuickSort)) then (inplaceSort cmp src)
   else
  let val half = (len div 2) in
  let val tup_56 = (splitAt half src) in
  let val src_l = (case tup_56 of (x__, _) => x__) in
  let val src_r = (case tup_56 of (_, x__) => x__) in
  let val tup_52 = (splitAt half tmp) in
  let val tmp_l = (case tup_52 of (x__, _) => x__) in
  let val tmp_r = (case tup_52 of (_, x__) => x__) in
  let val tmp_l1 = (writeSort2_seq cmp src_l tmp_l) in
  let val tmp_r1 = (writeSort2_seq cmp src_r tmp_r) in
  let val res = (writeMerge_seq cmp tmp_l1 tmp_r1 src) in res end end end end end end end end end end) end
and mergeSort'_seq cmp src =
  let val tmp = (copy src) in
  let val tmp2 = (writeSort1_seq cmp src tmp) in src end end
and mergeSort_seq cmp vec =
  let val vec2 = (copy vec) in
  let val vec3 = (mergeSort'_seq cmp vec2) in vec3 end end
and binarySearch' lo hi cmp vec query =
  let val n = (hi - lo) in
  (if (n = 0) then lo
   else
  let val mid = (lo + (n div 2)) in
  let val pivot = (nth vec mid) in
  let val tst = (cmp query pivot) in
  (if (tst < 0) then (binarySearch' lo mid cmp vec query)
   else
  (if (tst > 0) then (binarySearch' (mid + 1) hi cmp vec query)
   else mid)) end end end) end
and binarySearch cmp vec query = (binarySearch' 0 (length vec) cmp vec query)
and printVec_loop idx end_ vec f =
  (if (idx = end_) then ()
   else
  let val wildcard__187 = (f (ArraySlice.sub(vec , idx))) in
  let val wildcard__184 = (print ",") in (printVec_loop (idx + 1) end_ vec f) end end)
and printVec f vec =
  let val wildcard__178 = (print "[") in
  let val wildcard__176 = (printVec_loop 0 (ArraySlice.length vec) vec f) in
  let val wildcard__173 = (print "]") in () end end end
and print_newline wildcard__18 = print "\n"
and mergesort_debugPrint vec =
  let val wildcard__4 = (printVec (fn i => print(Int.toString(i))) vec) in
  let val wildcard__1 = (print_newline ()) in () end end
and print_space wildcard__20 = print " "
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
   else b)
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
and tail vec = (slice 1 ((ArraySlice.length vec) - 1) vec)
and head vec = (nth vec 0)
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
and length1 vec = (ArraySlice.length vec);
