// Monomorphic port of smergesort (+ writesort1/writesort2/merge) from
// csorts/mergesort.c.
// Changes from the generic: int64_t* + size_t n instead of slice_t (which
// wraps void* + total_elems + elt_size); direct int64_t comparison and
// assignment instead of __compar_fn_t + slice_inplace_update/slice_nth;
// memcpy instead of our_memcpy.  The CILKSORT branch is omitted since it
// is never active in the benchmark (CILKSORT == false by default).
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

// Forward declaration (writesort1 and writesort2 are mutually recursive).
static void writesort2_mono(int64_t *src, int64_t *tmp, size_t n);

// Sort src[0..n) in place, using tmp[0..n) as scratch.
// (Monomorphic writesort1.)
static void writesort1_mono(int64_t *src, int64_t *tmp, size_t n)
{
    if (n == 1) return;
    size_t half = n / 2;
    writesort2_mono(src,        tmp,        half);
    writesort2_mono(src + half, tmp + half, n - half);
    // merge tmp[0..half) and tmp[half..n) into src
    size_t i = 0, j = 0, k = 0;
    size_t n1 = half, n2 = n - half;
    while (i < n1 && j < n2) {
        if (tmp[i] <= tmp[n1 + j]) { src[k] = tmp[i];      i++; }
        else                        { src[k] = tmp[n1 + j]; j++; }
        k++;
    }
    while (i < n1) { src[k] = tmp[i];      i++; k++; }
    while (j < n2) { src[k] = tmp[n1 + j]; j++; k++; }
}

// Sort src[0..n) into tmp[0..n), using src as scratch.
// (Monomorphic writesort2.)
static void writesort2_mono(int64_t *src, int64_t *tmp, size_t n)
{
    if (n == 1) { tmp[0] = src[0]; return; }
    size_t half = n / 2;
    writesort1_mono(src,        tmp,        half);
    writesort1_mono(src + half, tmp + half, n - half);
    // merge src[0..half) and src[half..n) into tmp
    size_t i = 0, j = 0, k = 0;
    size_t n1 = half, n2 = n - half;
    while (i < n1 && j < n2) {
        if (src[i] <= src[n1 + j]) { tmp[k] = src[i];      i++; }
        else                        { tmp[k] = src[n1 + j]; j++; }
        k++;
    }
    while (i < n1) { tmp[k] = src[i];      i++; k++; }
    while (j < n2) { tmp[k] = src[n1 + j]; j++; k++; }
}

// Monomorphic smergesort: allocates and returns a sorted copy of arr[0..n).
int64_t *smergesort_mono(int64_t *arr, size_t n)
{
    int64_t *cpy = malloc(n * sizeof(int64_t));
    if (cpy == NULL) {
        fprintf(stderr, "smergesort_mono: couldn't allocate\n");
        exit(1);
    }
    memcpy(cpy, arr, n * sizeof(int64_t));

    int64_t *tmp = malloc(n * sizeof(int64_t));
    if (tmp == NULL) {
        fprintf(stderr, "smergesort_mono: couldn't allocate\n");
        exit(1);
    }

    writesort1_mono(cpy, tmp, n);

    free(tmp);
    return cpy;
}
