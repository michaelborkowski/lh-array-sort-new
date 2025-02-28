#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include "helpers.h"
#include "benchmarks.h"

// -----------------------------------------------------------------------------

// void quicksort_inplace_helper(void *_a, size_t n, size_t es);

template<typename T>
void quicksort_inplace_helper(T *_a, size_t n);

// void *quicksort_glibc(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp)
// {
//     // Copy into a fresh array.
//     char *cpy = (char *) malloc(total_elems * size);
//     if (cpy == NULL) {
//         fprintf(stderr, "insertionsort: couldn't allocate");
//         exit(1);
//     }
//     our_memcpy(cpy, (char *) pbase, (size * total_elems));

//     // Sort "cpy" in place.
//     quicksort_glibc_inplace(cpy, total_elems, size, cmp);
//     return cpy;
// }

// void quicksort_glibc_inplace(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp)
// {
//     qsort(pbase, total_elems, size, cmp);
// }

// void *quicksort(void *const pbase, size_t total_elems, size_t size)
// {
//     // Copy into a fresh array.
//     char *cpy = (char *) malloc(total_elems * size);
//     if (cpy == NULL) {
//         fprintf(stderr, "insertionsort: couldn't allocate");
//         exit(1);
//     }
//     our_memcpy(cpy, (char *) pbase, (size * total_elems));

//     // Sort "cpy" in place.
//     quicksort_inplace_cmp(cpy, total_elems, size, compare_int64s);
//     return cpy;
// }

// void *quicksort_cmp(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp)
// {
//     // Copy into a fresh array.
//     char *cpy = (char *) malloc(total_elems * size);
//     if (cpy == NULL) {
//         fprintf(stderr, "insertionsort: couldn't allocate");
//         exit(1);
//     }
//     our_memcpy(cpy, (char *) pbase, (size * total_elems));

//     // Sort "cpy" in place.
//     quicksort_inplace_cmp(cpy, total_elems, size, cmp);
//     return cpy;
// }

// void quicksort_inplace_cmp(void *_a, size_t n, size_t es, __compar_fn_t cmp)
// {
//     char *a = (char *) _a;
//     int j;
//     char *pi, *pj, *pn;
//     if (n <= 1) return;
//     pi = a + (rand() % n) * es;
//     SWAP(a, pi, es);
//     pi = a;
//     pj = pn = a + n * es;
//     for (;;) {
//         do pi += es; while (pi < pn && cmp(pi, a) < 0);
//         do pj -= es; while (cmp(pj, a) > 0);
//         if (pj < pi) break;
//         SWAP(pi, pj, es);
//     }
//     SWAP(a, pj, es);
//     j = (pj - a) / es;
//     quicksort_inplace_cmp(a, j, es, cmp);
//     quicksort_inplace_cmp(a + (j+1)*es, n-j-1, es, cmp);
// }

// void *quicksort_inplace(void *_a, size_t n, size_t es){

//     quicksort_inplace_helper(_a, n, es);
//     return _a;
// }

// void quicksort_inplace_helper(void *_a, size_t n, size_t es)
// {
//     char *a = (char *) _a;
//     int j;
//     char *pi, *pj, *pn;
//     if (n <= 1) return;
//     pi = a + (rand() % n) * es;
//     SWAP(a, pi, es);
//     pi = a;
//     pj = pn = a + n * es;
//     for (;;) {
//         do pi += es; while (pi < pn && compare_int64s(pi, a) < 0);
//         do pj -= es; while (compare_int64s(pj, a) > 0);
//         if (pj < pi) break;
//         SWAP(pi, pj, es);
//     }
//     SWAP(a, pj, es);
//     j = (pj - a) / es;
//     quicksort_inplace(a, j, es);
//     quicksort_inplace(a + (j+1)*es, n-j-1, es);
// }


template<typename T>
T *quicksort_inplace(T *_a, size_t n){

    quicksort_inplace_helper(_a, n);
    return _a;
}

template<typename T>
void quicksort_inplace_helper(T *_a, size_t n)
{
    T *a = (T *) _a;
    int j;
    int pi, pj, pn;
    if (n <= 1) return;
    pi = (rand() % n);
    SWAP2(a, 0, pi);
    pi = 0;
    pj = pn = n;
    for (;;) {
        do {pi++;} while (pi < pn && a[pi] < a[0]);
        do {pj--;} while (a[pj] > a[0]);
        if (pj < pi) break;
        SWAP2(a, pi, pj);
    }
    SWAP2(a, 0, pj);
    j = pj;
    quicksort_inplace_helper(a, j);
    quicksort_inplace_helper(&a[j+1], n-j-1);
}
