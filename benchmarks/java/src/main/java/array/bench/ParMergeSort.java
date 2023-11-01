package array.bench;

import java.util.*;
import java.util.concurrent.*;

public class ParMergeSort extends SeqMergeSort {
    private static final int SEQCUTOFF = 4096;
    @Override
    public void sort(int[] arr) {
        ForkJoinPool commonPool = ForkJoinPool.commonPool();
        startTimer();
        commonPool.invoke(new SortAction(arr, arr.length));
        endTimer();
    }

    private void doSeq(int[] a, int n) {
        seqMergeSort(a,n);
    }

    private class SortAction extends RecursiveAction {
        private int[] a;
        private int n;

        public SortAction(int[] a, int n) {
            this.a = a;
            this.n = n;
        }
        @Override
        protected void compute() {
            if (a.length < SEQCUTOFF) {
                doSeq(a,n);
            } else {
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
                List<SortAction> recursiveActions = new ArrayList<SortAction>();
                recursiveActions.add(new SortAction(l, mid));
                recursiveActions.add(new SortAction(r, n - mid));
                ForkJoinTask.invokeAll(recursiveActions);
                merge(a, l, r, mid, n - mid);
            }
        }
    }
    @Override
    public String toString() {
        return "ParMergeSort";
    }
}
