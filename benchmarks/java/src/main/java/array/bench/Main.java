package array.bench;

public class Main {
    private static final int NUM_ITERS = 20;
    public static void main(String[] args) {
        assert args.length == 2 : "Wrong argument count";
        int n = Integer.parseInt(args[1]);
        BenchSort s;
        if (args[0].equals("insertion")) {
            s = new InsertionSort();
        } else if (args[0].equals("seqmergesort")) {
            s = new SeqMergeSort();
        } else if (args[0].equals("parmergesort")) {
            s = new ParMergeSort();
        } else if (args[0].equals("quicksort")) {
            s = new QuickSort();
        } else {
            System.err.println("Unexpected sort type: " + args[0]);
            return;
        }
        BenchRunner runner = new BenchRunner(s);
        System.out.println("BENCHMARK: " + s.toString());
        System.out.println("TOTAL_ELEMS: " + n);
        System.out.println("ITERS: " + NUM_ITERS);
        long time = 0;
        for (int i = -5; i < NUM_ITERS; i++) {
            runner.generateArray(n);
            long thisTime = runner.runBenchmark();
            if (i >= 0) {
                time += thisTime;
            }
            System.out.println("iter[" + i + "] = " + thisTime);
        }
        System.out.println("BATCHTIME: " + time);
        System.out.println("SELFTIMED: " + time / NUM_ITERS);
    }
}
