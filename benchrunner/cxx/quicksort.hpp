#pragma once

#include "benchmarks.h"
#include <cstdlib>
#include <utility>

// -----------------------------------------------------------------------------

template<typename T>
static void quicksort_inplace_helper(T *a, size_t n);

template<typename T>
inline T *quicksort_inplace(T *a, size_t n){
    quicksort_inplace_helper(a, n);
    return a;
}

template<typename T>
static void quicksort_inplace_helper(T *a, size_t n)
{
    if (n <= 1) return;

    // Hoare partition scheme
    int pivot_idx = (rand() % n);
    std::swap(a[0], a[pivot_idx]);

    int i = 0;
    int j = n;
    for (;;) {
        do { i++; } while (i < n && a[i] < a[0]);
        do { j--; } while (a[j] > a[0]);
        if (j < i) break;
        std::swap(a[i], a[j]);
    }
    std::swap(a[0], a[j]);
    quicksort_inplace_helper(a, j);
    quicksort_inplace_helper(a + j + 1, n - j - 1);
}