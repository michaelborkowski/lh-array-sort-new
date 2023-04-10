#ifndef _BENCHMARKS_H
#define _BENCHMARKS_H

#include <stdlib.h>
#include <stdint.h>

// Copied from stdlib.h for reference.
typedef int (*__compar_fn_t) (const void *, const void *);

// Sorting algorithms.
void *insertionsort_glibc (void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp);
void *insertionsort_glibc_inplace(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp);
void *insertionsort(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp);
void *insertionsort_inplace(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp);
void *quicksort_inplace(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp);
void *mergesort (void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp);
void *mergesort_par(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp);
void *cilksort (void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp);
void *cilksort_par(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp);

// Microbenchmarks.
int64_t* __attribute__ ((noinline)) fill_array_seq(size_t total_elems, int64_t val);
int64_t* __attribute__ ((noinline)) fill_array_par(size_t total_elems, int64_t val);
int64_t* __attribute__ ((noinline)) fill_array_rand_seq(size_t total_elems);
int64_t* __attribute__ ((noinline)) fill_array_ones_seq(size_t total_elems);
int64_t __attribute__ ((noinline)) sum_array_seq(size_t total_elems, int64_t *nums);
int64_t __attribute__ ((noinline)) sum_array_par(size_t total_elems, int64_t *nums);
void __attribute__ ((noinline)) copy_seq(void *dst, void *src, size_t nbytes);
void __attribute__ ((noinline)) copy_par(void *dst, void *src, size_t nbytes);
int64_t fib(int64_t n);
int64_t fib_par(int64_t n);

#endif
