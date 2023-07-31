package array.bench;

public class InsertionSort extends BenchSort {
    @Override
    public void sort(int[] arr) {
        startTimer();
        int n = arr.length;
        for (int i = 1; i < n; i++) {
            int k = arr[i];
            int j = i - 1;
            while (j >= 0 && arr[j] > k) {
                arr[j + 1] = arr[j];
                j--;
            }
            arr[j + 1] = k;
        }
        endTimer();
    }

    @Override
    public String toString() {
        return "InsertionSort";
    }
}
