#include "microbench.h"

// -----------------------------------------------------------------------------

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

void fill_array_seq_(size_t total_elems, int64_t val, int64_t *nums) {
    int64_t *elt = nums;
    for (uint64_t i = 0; i <= total_elems-1; i++) {
        elt = (int64_t*) nums + i;
        *elt = val;
    }
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


void __attribute__ ((noinline)) copy_seq(void *dst, void *src, size_t nbytes)
{
    our_memcpy(dst, src, nbytes);
}

int64_t fib(int64_t n)
{
    if (n < 2) {
        return 1;
    }
    return fib (n-1) + fib(n-2);
}
