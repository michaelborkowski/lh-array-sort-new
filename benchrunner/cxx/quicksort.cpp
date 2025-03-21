#include "benchmarks.h"

// -----------------------------------------------------------------------------

template<typename T> inline void quicksort_inplace_helper(T *_a, size_t n);

template<typename T>
T *quicksort_inplace(T *_a, size_t n){

    quicksort_inplace_helper(_a, n);
    return _a;
}

template<typename T>
static inline void SWAP2(T *a, int i, int j)
{
    T _tmp = a[i];
    a[i] = a[j];
    a[j] = _tmp;
}

template<typename T>
inline void quicksort_inplace_helper(T *_a, size_t n)
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
