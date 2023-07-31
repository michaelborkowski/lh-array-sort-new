package array.bench;

public class SeqMergeSort extends BenchSort {
    @Override
    public void sort(int[] arr) {
        startTimer();
        seqMergeSort(arr, arr.length);
        endTimer();
    }

    protected void merge(int[] a, int[] l, int[] r, int left, int right) {
        int i = 0, j = 0, k = 0;
        while (i < left && j < right) {
            if (l[i] <= r[j]) {
                a[k++] = l[i++];
            }
            else {
                a[k++] = r[j++];
            }
        }
        while (i < left) {
            a[k++] = l[i++];
        }
        while (j < right) {
            a[k++] = r[j++];
        }
    }

    protected void seqMergeSort(int[] a, int n) {
        if (n < 2) {
            return;
        }
        int mid = n / 2;
        int[] l = new int[mid];
        int[] r = new int[n - mid];

        for (int i = 0; i < mid; i++) {
            l[i] = a[i];
        }
        for (int i = mid; i < n; i++) {
            r[i - mid] = a[i];
        }
        seqMergeSort(l, mid);
        seqMergeSort(r, n - mid);

        merge(a, l, r, mid, n - mid);
    }
//
//    public static void merge(int[] arr, int start, int mid, int end) {
//        int i = start;
//        int j = mid;
//        int k = mid + 1;
//        if (arr[j] <= arr[k]) {
//            return;
//        }
//        while (i <= j && k <= end) {
//            if (arr[i] <= arr[k]) {
//                i++;
//            } else {
//                int v = arr[k];
//                int x = k;
//                while (x != i) {
//                    arr[x] = arr[x - 1];
//                    x--;
//                }
//                arr[i] = v;
//                i++;
//                j++;
//                k++;
//            }
//        }
//    }
//
//    private void seqMergeSort(int[] arr, int l, int r) {
//        if (l < r) {
//            int m = l + (r - l) / 2;
//            seqMergeSort(arr, l, m);
//            seqMergeSort(arr, m + 1, r);
//            SeqMergeSort.merge(arr, l, m, r);
//        }
//    }

    @Override
    public String toString() {
        return "SeqMergeSort";
    }
}
