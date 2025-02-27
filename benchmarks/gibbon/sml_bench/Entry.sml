fun get_rand (n : int) : int =
  let
    val t = Time.now()
    val i = Real.round (Time.toReal t)
  in
    Word64.toInt (Word64.mod (Util.hash64 (Word64.fromInt i), Word64.fromInt n))
  end
fun get_rand_int _ = get_rand(2147483647)

(* Parameters *)
val (iters, arrsize) =
  case List.map (valOf o Int.fromString) (CommandLine.arguments()) of
      [iters, arrsize] => (iters, arrsize)
    | _ => raise Fail "Entry"

fun mk_rand_slice () =
  ArraySlice.full(Array.tabulate(arrsize, get_rand_int))

val _ = print "Insertion Sort:\n"
val _ = print_bench iters arrsize (isort2 compare_int) mk_rand_slice
val _ = print "Mergesort:\n"
val _ = print_bench iters arrsize (msort_ compare_int) mk_rand_slice
val _ = print "\nQuicksort\n"
val _ = print_bench iters arrsize (fn arr => quickSort arr compare_int) mk_rand_slice
