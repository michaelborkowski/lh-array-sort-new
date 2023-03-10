#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <errno.h>

#include <cilk/cilk.h>

// -----------------------------------------------------------------------------

int64_t* __attribute__ ((noinline)) fill_array_seq(size_t total_elems, int64_t val)
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
        *elt = val;
    }
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
    int64_t *elt = nums;
    cilk_for (uint64_t i = 0; i <= total_elems-1; i++) {
        elt = (int64_t*) nums + i;
        *elt = val;
    }
    return nums;
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
        *elt = (rand() % 1024);
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
    int64_t sum = 0;
    int64_t *elt = nums;
    cilk_for (uint64_t i = 0; i <= total_elems-1; i++) {
        elt = (int64_t*) (nums + i);
        sum += *elt;
    }
    return sum;
}
