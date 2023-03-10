#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include "helpers.h"
#include "benchmarks.h"

// -----------------------------------------------------------------------------

#define GOTO_INSERTION 10

void writesort1(__compar_fn_t cmp, slice_t src, slice_t tmp);
void writesort2(__compar_fn_t cmp, slice_t src, slice_t tmp);
void merge(__compar_fn_t cmp, slice_t left, slice_t right, slice_t dst);

void *mergesort (void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp)
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
    writesort1(cmp, cpy_sl, tmp_sl);

    return cpy;
}

// Uses "tmp" to sort "src" in place.
void writesort1(__compar_fn_t cmp, slice_t src, slice_t tmp)
{
    size_t len = slice_length(&src);
    if (len == 1) {
        return;
    }
    // if (len < GOTO_INSERTION) {
    //     insertionsort_glibc_inplace(src.base, src.total_elems, src.elt_size, cmp);
    // }
    size_t half = len / 2;
    slice_prod_t splitsrc = slice_split_at(&src, half);
    slice_prod_t splittmp = slice_split_at(&tmp, half);
    writesort2(cmp, splitsrc.left, splittmp.left);
    writesort2(cmp, splitsrc.right, splittmp.right);
    merge(cmp, splittmp.left, splittmp.right, src);
    return;
}

// Uses "src" to sort "tmp" in place.
void writesort2(__compar_fn_t cmp, slice_t src, slice_t tmp)
{
    size_t len = slice_length(&src);
    if (len == 1) {
        slice_copy(&src, &tmp);
        return;
    }
    // if (len < GOTO_INSERTION) {
    //     slice_copy(&src, &tmp);
    //     insertionsort_glibc_inplace(tmp.base, tmp.total_elems, tmp.elt_size, cmp);
    // }
    size_t half = len / 2;
    slice_prod_t splitsrc = slice_split_at(&src, half);
    slice_prod_t splittmp = slice_split_at(&tmp, half);
    writesort1(cmp, splitsrc.left, splittmp.left);
    writesort1(cmp, splitsrc.right, splittmp.right);
    merge(cmp, splitsrc.left, splitsrc.right, tmp);
    return;
}

void merge(__compar_fn_t cmp, slice_t left, slice_t right, slice_t dst)
{
    size_t i=0, j=0, k=0;
    size_t n1 = slice_length(&left);
    size_t n2 = slice_length(&right);

    void *elt_l, *elt_r;

    while (i < n1 && j < n2) {
        elt_l = slice_nth(&left, i);
        elt_r = slice_nth(&right, j);
        if ((*cmp)(elt_l, elt_r) <= 0) {
            slice_inplace_update(&dst, k, elt_l);
            i++;
        } else {
            slice_inplace_update(&dst, k, elt_r);
            j++;
        }
        k++;
    }

    while (i < n1) {
        elt_l = slice_nth(&left, i);
        slice_inplace_update(&dst, k, elt_l);
        i++;
        k++;
    }

    while (j < n2) {
        elt_r = slice_nth(&right, j);
        slice_inplace_update(&dst, k, elt_r);
        j++;
        k++;
    }

    return;
}
