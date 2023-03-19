#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include "helpers.h"

// -----------------------------------------------------------------------------

void quicksort_inplace(void *_a, size_t n, size_t es, __compar_fn_t cmp)
{
    char *a = _a;
    int j;
    char *pi, *pj, *pn;
    if (n <= 1) return;
    pi = a + (rand() % n) * es;
    SWAP(a, pi, es);
    pi = a;
    pj = pn = a + n * es;
    for (;;) {
        do pi += es; while (pi < pn && cmp(pi, a) < 0);
        do pj -= es; while (cmp(pj, a) > 0);
        if (pj < pi) break;
        SWAP(pi, pj, es);
    }
    SWAP(a, pj, es);
    j = (pj - a) / es;
    quicksort_inplace(a, j, es, cmp);
    quicksort_inplace(a + (j+1)*es, n-j-1, es, cmp);
}
