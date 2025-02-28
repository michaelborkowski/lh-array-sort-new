#ifdef CILK
#include "microbench.h"
#include <cilk/cilk.h>
#include "par_helpers.h"

void fill_array_par_(size_t total_elems, int64_t val, int64_t *nums);

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

void __attribute__ ((noinline)) copy_par(void *dst, void *src, size_t nbytes)
{
    our_memcpy_par(dst, src, nbytes);
}

int64_t fib_par(int64_t n)
{
    if (n <= 32) {
        return fib(n);
    }

    #ifdef CILK
    int64_t x = cilk_spawn fib_par(n-1);
    int64_t y = fib_par(n-2);
    cilk_sync;
    #else
    int64_t x = fib_par(n-1);
    int64_t y = fib_par(n-2);
    #endif

    return x+y;
}
#endif
