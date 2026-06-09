// Simplified port of the quicksort core from
// Data.Vector.Algorithms.Intro (vector-algorithms-0.9.1.0).
//
// Keeps the two key algorithmic choices from vector-algorithms verbatim:
//   1. sort3ByIndex(a, midpoint, lo, hi-1): 3-element sorting network that
//      places min at midpoint, median at lo (= pivot), max at hi-1.
//   2. partitionBy / partUp / partDown: scan forward while < pivot,
//      backward while > pivot, swap; median at lo and max at hi-1 act as
//      sentinels bounding both scans.
//
// Removed from the original introsort:
//   - heapsort fallback at depth 2*lg(n)
//   - insertion sort pass for segments < 18
#include <stdint.h>
#include <stdlib.h>

static inline void swap64(int64_t *a, int64_t *b)
{
    int64_t t = *a; *a = *b; *b = t;
}

/* 3-element sorting network: after this a[i] <= a[j] <= a[k].
 * Equivalent to Data.Vector.Algorithms.Optimal.sort3ByIndex. */
static inline void sort3_by_index(int64_t *a, size_t i, size_t j, size_t k)
{
    if (a[i] > a[j]) swap64(a+i, a+j);
    if (a[j] > a[k]) swap64(a+j, a+k);
    if (a[i] > a[j]) swap64(a+i, a+j);
}

/* Partition a[lo..hi) around pivot.  Returns mid such that
 * a[lo..mid) may include elts swapped from right (all >= pivot originally
 * seen by partDown) and a[mid..hi) >= pivot.
 *
 * Direct translation of partitionBy / partUp / partDown from Intro.hs:
 *   partUp  advances l  while *l < pivot  (stops at first >= pivot)
 *   partDown retreats r while *r > pivot  (stops at first <= pivot, then swaps) */
static size_t partition_by(int64_t *a, int64_t pivot, size_t lo, size_t hi)
{
    int64_t *l = a + lo;
    int64_t *r = a + hi - 1;

    for (;;) {
        while (l <= r && *l < pivot) l++;
        if (l > r) break;
        while (l < r  && *r > pivot) r--;
        if (l >= r) break;
        swap64(l++, r--);
    }
    return (size_t)(l - a);
}

static void qs(int64_t *a, size_t lo, size_t hi)
{
    /* Tail-call on the larger half to keep stack depth O(log n). */
    while (hi - lo >= 2) {
        size_t len = hi - lo;

        if (len == 2) {
            if (a[lo] > a[lo+1]) swap64(a+lo, a+lo+1);
            return;
        }

        /* sort3_by_index(a, midpoint, lo, hi-1):
         *   min  → a[midpoint]   (don't care)
         *   median → a[lo]        = pivot
         *   max  → a[hi-1]        = right sentinel for partDown */
        size_t m = lo + (len >> 1);
        sort3_by_index(a, m, lo, hi - 1);

        int64_t p = a[lo];
        size_t mid = partition_by(a, p, lo + 1, hi);
        /* Put pivot at its final position. */
        swap64(a + lo, a + mid - 1);
        /* a[lo..mid-1) < p,  a[mid-1] = p,  a[mid..hi) >= p */

        /* Recurse on the smaller partition; loop on the larger. */
        if (mid - 1 - lo <= hi - mid) {
            qs(a, lo, mid - 1);
            lo = mid;
        } else {
            qs(a, mid, hi);
            hi = mid - 1;
        }
    }
}

int64_t *quicksort_mono_inplace(int64_t *arr, size_t n)
{
    if (n < 2) return arr;
    qs(arr, 0, n);
    return arr;
}
