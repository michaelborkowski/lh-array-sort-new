fun merge cmp ([], ys) = ys
  | merge cmp (xs, []) = xs
  | merge cmp (xs as x::xs', ys as y::ys') =
    case cmp (x, y) of
        GREATER => y :: merge cmp (xs, ys')
      | _       => x :: merge cmp (xs', ys)

fun sort cmp [] = []
  | sort cmp [x] = [x]
  | sort cmp xs =
    let
      val ys = List.take (xs, length xs div 2)
      val zs = List.drop (xs, length xs div 2)
    in
      merge cmp (sort cmp ys, sort cmp zs)
    end

fun median ls =
    let
      val n = List.length ls
      val idx = n div 2
      val ls2 = sort Time.compare ls
    in
      List.nth (ls2, idx)
    end

fun dotrial f arg =
    let
      val _  = MLton.GC.collect ()
      val t0 = Time.now()
      val result = f (arg())
      val t1 = Time.now()
      val diff = Time.- (t1, t0)
      val _ = print("iter time: " ^ Time.fmt 8 diff ^ "\n")
    in
      (result, diff)
    end

fun bench iters f arg =
    let
      val tups = List.map (fn _ => dotrial f arg) (List.tabulate (iters, (fn i => i)))
      val (results, times) = ListPair.unzip tups
      val batch = List.foldr (fn (n, acc) => Time.+ (n, acc)) Time.zeroTime times
    in
      (List.nth (results, 0), batch, median times)
    end

fun print_bench iters size f arg =
  let
    val (result, batch, t) = bench iters f arg
    val _ = print ("ITERS: " ^ Int.toString iters ^ "\n")
    val _ = print ("SIZE: " ^ Int.toString size ^ "\n")
    val _ = print ("BATCHTIME: " ^ Time.fmt 8 batch ^ "\n")
    val _ = print ("SELFTIMED: " ^ Time.fmt 8 t ^ "\n")
  in
    result
  end
