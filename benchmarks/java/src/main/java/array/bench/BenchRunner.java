package array.bench;
import java.util.*;
public class BenchRunner {
    private BenchSort sorter;
    private int[] arr;
    private static final long SEED = 42;
    private static final int BOUND = 10000000;

    public BenchRunner(BenchSort sorter) {
        this.sorter = sorter;
    }

    public long runBenchmark() {
        assert !verifySorted() : "Initial array is sorted";
        sorter.sort(arr);
        assert verifySorted() : "Resulting array is not sorted";
        return sorter.getElapsedTime();
    }

    public void generateArray(int n) {
        assert n > 0 : "Array length must be positive";
        Random r = new Random(SEED);
        arr = new int[n];
        for (int i = 0; i < n; i++) {
            arr[i] = r.nextInt(BOUND);
        }
    }

    public boolean verifySorted() {
        int n = arr.length;
        int x = 0;
        for (int i = 0; i < n; i++) {
            if (arr[i] < x) {
                return false;
            } else {
                x = arr[i];
            }
        }
        return true;
    }
}
