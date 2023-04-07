#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <errno.h>
#include <cilk/cilk.h>

#include "helpers.h"

// -----------------------------------------------------------------------------

void fill_array_seq_(size_t total_elems, int64_t val, int64_t *nums);
void fill_array_par_(size_t total_elems, int64_t val, int64_t *nums);

int64_t* __attribute__ ((noinline)) fill_array_seq(size_t total_elems, int64_t val)
{
    void *nums;
    nums = (int64_t*) malloc(total_elems * sizeof(int64_t));
    if (nums == NULL) {
        fprintf(stderr, "Couldn't allocate memory for output array.\n");
        return NULL;
    }
    fill_array_seq_(total_elems, val, nums);
    return nums;
}

int64_t* __attribute__ ((noinline)) fill_array_par(size_t total_elems, int64_t val)
{
    void *nums;
    nums = (int64_t*) malloc(total_elems * sizeof(int64_t));
    if (nums == NULL) {
        fprintf(stderr, "Couldn't allocate memory for output array.\n");
        return NULL;
    }
    fill_array_par_(total_elems, val, nums);
    return nums;
}

void fill_array_seq_(size_t total_elems, int64_t val, int64_t *nums) {
    int64_t *elt = nums;
    for (uint64_t i = 0; i <= total_elems-1; i++) {
        elt = (int64_t*) nums + i;
        *elt = val;
    }
    return;
}

void fill_array_par_(size_t total_elems, int64_t val, int64_t *nums)
{
    if (total_elems < 8192) {
        fill_array_seq_(total_elems, val, nums);
        return;
    }
    size_t half = total_elems / 2;
    cilk_spawn fill_array_par_(half, val, nums);
    int64_t *nums2 = (int64_t*) ((char*)nums + (half * sizeof(int64_t)));
    fill_array_par_(total_elems - half, val, nums2);
    cilk_sync;
    return;
}

int64_t* __attribute__ ((noinline)) fill_array_rand_seq(size_t total_elems)
{
    void *nums;
    nums = (int64_t*) malloc(total_elems * sizeof(int64_t));
    if (nums == NULL) {
        fprintf(stderr, "Couldn't allocate memory for output array.\n");
        return NULL;
    }
    int64_t *elt = nums;
    for (uint64_t i = 0; i <= total_elems-1; i++) {
        elt = (int64_t*) nums + i;
        *elt = rand();
    }
    return nums;
}

int64_t* __attribute__ ((noinline)) fill_array_ones_seq(size_t total_elems)
{
    return fill_array_seq(total_elems, 1);
}

int64_t __attribute__ ((noinline)) sum_array_seq(size_t total_elems, int64_t *nums)
{
    int64_t sum = 0;
    int64_t *elt = nums;
    for (uint64_t i = 0; i <= total_elems-1; i++) {
        elt = (int64_t*) (nums + i);
        sum += *elt;
    }
    return sum;
}

int64_t __attribute__ ((noinline)) sum_array_par(size_t total_elems, int64_t *nums)
{
    if (total_elems < 8192) {
        return sum_array_seq(total_elems, nums);
    }
    size_t half = total_elems / 2;
    int64_t sum1 = cilk_spawn sum_array_par(half, nums);
    int64_t *nums2 = (int64_t*) ((char*)nums + (half * sizeof(int64_t)));
    int64_t sum2 = sum_array_par(total_elems - half, nums2);
    cilk_sync;
    return sum1 + sum2;
}


void __attribute__ ((noinline)) copy_seq(void *dst, void *src, size_t nbytes)
{
    our_memcpy(dst, src, nbytes);
}

void __attribute__ ((noinline)) copy_par(void *dst, void *src, size_t nbytes)
{
    our_memcpy_par(dst, src, nbytes);
}
