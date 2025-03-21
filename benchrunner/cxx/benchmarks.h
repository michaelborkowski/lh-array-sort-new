#ifndef _BENCHMARKS_H
#define _BENCHMARKS_H

#include <stdlib.h>
#include <stdint.h>
#include <iostream>
#include <chrono>

// Copied from stdlib.h for reference.
typedef int (*__compar_fn_t) (const void *, const void *);

// Sorting algorithms.
template<typename T> T *insertionsort_inplace(T *pbase, size_t total_elems);
template<typename T> T *quicksort_inplace(T *_a, size_t n);
template <typename T> T *bottomUpMergeSort(T *a, T *b, int n);
template <typename T> void bottomUpMerge(T *a, int left, int right, int end, T *b);
template <typename T> void copyArray(T *b, T* a, int n);

// Relating to C++ templatized versions
extern "C" {
    extern int64_t *bottom_up_merge_sort_cxx_int(int64_t *pbase, size_t total_elems);
    extern int64_t *insertionsort_cxx_int(int64_t *pbase, size_t total_elems);
    extern int64_t *quicksort_cxx_int(int64_t *pbase, size_t total_elems);
}

// Microbenchmarks.
int64_t* __attribute__ ((noinline)) fill_array_rand_seq(size_t total_elems);

#endif
