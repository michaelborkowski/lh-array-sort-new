#ifdef CILK
#include <cilk/cilk.h>
#include "par_helpers.h"
#include "mergesort_common.h"


// Parallel.
void writesort1_par(slice_t src, slice_t tmp);
void writesort2_par(slice_t src, slice_t tmp);
void merge_par(slice_t left, slice_t right, slice_t dst);
size_t binary_search(slice_t *sl, void *query);

// Whether this mergesort should actually be cilksort.
static bool CILKSORT = false;

// Global.
static __compar_fn_t CMP = NULL;

// Parallel cilksort.
void *cilksort_par(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp)
{
    CILKSORT = true;
    void *sorted = mergesort_par(pbase, total_elems, size, cmp);
    CILKSORT = false;
    return sorted;
}

// Parallel mergesort.
void *mergesort_par(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp)
{
    // Copy into a fresh array.
    char *cpy = malloc(total_elems * size);
    if (cpy == NULL) {
        fprintf(stderr, "mergesort: couldn't allocate");
        exit(1);
    }
    our_memcpy_par(cpy, (char *) pbase, (size * total_elems));

    // Temporary buffer.
    char *tmp = malloc(total_elems * size);
    if (tmp == NULL) {
        fprintf(stderr, "mergesort: couldn't allocate");
        exit(1);
    }

    slice_t cpy_sl = (slice_t) {cpy, total_elems, size};
    slice_t tmp_sl = (slice_t) {tmp, total_elems, size};

    CMP = cmp;
    writesort1_par(cpy_sl, tmp_sl);
    CMP = NULL;

    return cpy;
}

// Uses "tmp" to sort "src" in place.
void writesort1_par(slice_t src, slice_t tmp)
{
    size_t len = slice_length(&src);
    if (CILKSORT && (len < INSERTIONSIZE)) {
        // insertionsort_inplace(src.base, src.total_elems, src.elt_size, CMP);
        qsort(src.base, src.total_elems, src.elt_size, CMP);
        // quicksort_inplace(src.base, src.total_elems, src.elt_size, CMP);
        return;
    }
    if (len < SEQCUTOFF) {
        writesort1(src, tmp);
        return;
    }
    if (len == 1) {
        return;
    }
    size_t half = len / 2;
    slice_prod_t splitsrc = slice_split_at(&src, half);
    slice_prod_t splittmp = slice_split_at(&tmp, half);

    cilk_spawn writesort2_par(splitsrc.left, splittmp.left);
    writesort2_par(splitsrc.right, splittmp.right);
    cilk_sync;

    merge_par(splittmp.left, splittmp.right, src);
    return;
}

// Uses "src" to sort "tmp" in place.

void writesort2_par(slice_t src, slice_t tmp)
{
    size_t len = slice_length(&src);
    if (CILKSORT && (len < INSERTIONSIZE)) {
        slice_copy(&src, &tmp);
        // insertionsort_inplace(tmp.base, tmp.total_elems, tmp.elt_size, CMP);
        qsort(tmp.base, tmp.total_elems, tmp.elt_size, CMP);
        // quicksort_inplace(src.base, src.total_elems, src.elt_size, CMP);
        return;
    }
    if (len < SEQCUTOFF) {
        writesort2(src, tmp);
        return;
    }
    if (len == 1) {
        slice_copy(&src, &tmp);
        return;
    }
    size_t half = len / 2;
    slice_prod_t splitsrc = slice_split_at(&src, half);
    slice_prod_t splittmp = slice_split_at(&tmp, half);

    cilk_spawn writesort1_par(splitsrc.left, splittmp.left);
    writesort1_par(splitsrc.right, splittmp.right);
    cilk_sync;

    merge_par(splitsrc.left, splitsrc.right, tmp);
    return;
}

// -----------------------------------------------------------------------------

void merge_par(slice_t left, slice_t right, slice_t dst)
{
    size_t len = slice_length(&dst);
    if (len < SEQCUTOFF) {
        merge(left, right, dst);
        return;
    }
    size_t n1 = slice_length(&left);
    size_t n2 = slice_length(&right);
    if (n1 == 0) {
        slice_copy_par(&right, &dst);
        return;
    }
    size_t mid1 = n1 / 2;
    void *pivot = slice_nth(&left, mid1);
    size_t mid2 = binary_search(&right, pivot);
    slice_t left_l = slice_narrow(&left, 0, mid1);
    slice_t left_r = slice_narrow(&left, mid1+1, (n1-(mid1+1)));
    slice_t right_l = slice_narrow(&right, 0, mid2);
    slice_t right_r = slice_narrow(&right, mid2, n2-mid2);
    slice_inplace_update(&dst, mid1+mid2, pivot);
    slice_t dst_l = slice_narrow(&dst, 0, mid1+mid2);
    slice_t dst_r = slice_narrow(&dst, mid1+mid2+1, len-(mid1+mid2+1));

    cilk_spawn merge_par(left_l, right_l, dst_l);
    merge_par(left_r, right_r, dst_r);
    cilk_sync;

    return;
}
#endif
