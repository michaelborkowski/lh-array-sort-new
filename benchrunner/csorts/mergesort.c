#include "mergesort_common.h"

// -----------------------------------------------------------------------------

// Whether this mergesort should actually be cilksort.
static bool CILKSORT = false;

// Global.
static __compar_fn_t CMP = NULL;

// Sequential cilksort.
void *cilksort(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp)
{
    CILKSORT = true;
    void *sorted = smergesort_cmp(pbase, total_elems, size, cmp);
    CILKSORT = false;
    return sorted;
}

// Sequential mergesort.
void *smergesort(void *const pbase, size_t total_elems, size_t size)
{
    // Copy into a fresh array.
    char *cpy = malloc(total_elems * size);
    if (cpy == NULL) {
        fprintf(stderr, "mergesort: couldn't allocate");
        exit(1);
    }
    our_memcpy(cpy, (char *) pbase, (size * total_elems));

    // Temporary buffer.
    char *tmp = malloc(total_elems * size);
    if (tmp == NULL) {
        fprintf(stderr, "mergesort: couldn't allocate");
        exit(1);
    }

    slice_t cpy_sl = (slice_t) {cpy, total_elems, size};
    slice_t tmp_sl = (slice_t) {tmp, total_elems, size};

    CMP = compare_int64s;
    writesort1(cpy_sl, tmp_sl);
    CMP = NULL;

    return cpy;
}

// Sequential mergesort.
void *smergesort_cmp(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp)
{
    // Copy into a fresh array.
    char *cpy = malloc(total_elems * size);
    if (cpy == NULL) {
        fprintf(stderr, "mergesort: couldn't allocate");
        exit(1);
    }
    our_memcpy(cpy, (char *) pbase, (size * total_elems));

    // Temporary buffer.
    char *tmp = malloc(total_elems * size);
    if (tmp == NULL) {
        fprintf(stderr, "mergesort: couldn't allocate");
        exit(1);
    }

    slice_t cpy_sl = (slice_t) {cpy, total_elems, size};
    slice_t tmp_sl = (slice_t) {tmp, total_elems, size};

    CMP = cmp;
    writesort1(cpy_sl, tmp_sl);
    CMP = NULL;

    return cpy;
}

// -----------------------------------------------------------------------------

// Uses "tmp" to sort "src" in place.
void writesort1(slice_t src, slice_t tmp)
{
    size_t len = slice_length(&src);
    if (CILKSORT && (len < INSERTIONSIZE)) {
        // insertionsort_inplace(src.base, src.total_elems, src.elt_size, CMP);
        qsort(src.base, src.total_elems, src.elt_size, CMP);
        // quicksort_inplace(src.base, src.total_elems, src.elt_size, CMP);
        return;
    }
    if (len == 1) {
        return;
    }
    size_t half = len / 2;
    slice_prod_t splitsrc = slice_split_at(&src, half);
    slice_prod_t splittmp = slice_split_at(&tmp, half);
    writesort2(splitsrc.left, splittmp.left);
    writesort2(splitsrc.right, splittmp.right);
    merge(splittmp.left, splittmp.right, src);
    return;
}

// Uses "src" to sort "tmp" in place.
void writesort2(slice_t src, slice_t tmp)
{
    size_t len = slice_length(&src);
    if (CILKSORT && (len < INSERTIONSIZE)) {
        slice_copy(&src, &tmp);
        // insertionsort_inplace(tmp.base, tmp.total_elems, tmp.elt_size, CMP);
        qsort(tmp.base, tmp.total_elems, tmp.elt_size, CMP);
        // quicksort_inplace(tmp.base, tmp.total_elems, tmp.elt_size, CMP);
        return;
    }
    if (len == 1) {
        slice_copy(&src, &tmp);
        return;
    }
    size_t half = len / 2;
    slice_prod_t splitsrc = slice_split_at(&src, half);
    slice_prod_t splittmp = slice_split_at(&tmp, half);
    writesort1(splitsrc.left, splittmp.left);
    writesort1(splitsrc.right, splittmp.right);
    merge(splitsrc.left, splitsrc.right, tmp);
    return;
}

size_t binary_search(slice_t *sl, void *query)
{
    size_t lo = 0;
    size_t hi = slice_length(sl);

    size_t n, mid;
    void *pivot;
    int tst;

    while (hi > lo) {
        n = hi - lo;
        mid = lo + (n/2);
        pivot = slice_nth(sl, mid);
        tst = (*CMP)(query, pivot);
        if (tst == 0) {
            return mid;
        }
        if (tst < 0) {
            hi = mid;
        } else {
            lo = mid+1;
        }
    }

    return lo;
}

void merge(slice_t left, slice_t right, slice_t dst)
{
    size_t i=0, j=0, k=0;
    size_t n1 = slice_length(&left);
    size_t n2 = slice_length(&right);

    void *elt_l, *elt_r;

    while (i < n1 && j < n2) {
        elt_l = slice_nth(&left, i);
        elt_r = slice_nth(&right, j);
        if ((*CMP)(elt_l, elt_r) <= 0) {
            slice_inplace_update(&dst, k, elt_l);
            i++;
        } else {
            slice_inplace_update(&dst, k, elt_r);
            j++;
        }
        k++;
    }

    // Use slice_copy.
    while (i < n1) {
        elt_l = slice_nth(&left, i);
        slice_inplace_update(&dst, k, elt_l);
        i++;
        k++;
    }

    // Use slice_copy.
    while (j < n2) {
        elt_r = slice_nth(&right, j);
        slice_inplace_update(&dst, k, elt_r);
        j++;
        k++;
    }

    return;
}
