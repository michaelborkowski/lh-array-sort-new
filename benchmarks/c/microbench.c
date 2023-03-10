#include "cbench.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#include <cilk/cilk.h>

int __attribute__ ((noinline)) fill_array_seq(uint32_t N, int64_t x)
{
    void *array;
    array = (int64_t*) malloc(N * sizeof(int64_t));
    if (array == NULL) {
        fprintf(stderr, "Couldn't allocate memory for input array.\n");
    }
    int64_t *elt = array;
    for (uint32_t i = 0; i <= N-1; i++) {
        elt = (int64_t*) array + i;
        *elt = x;
    }
    free(array);
}

int __attribute__ ((noinline)) fill_array_par(uint32_t N, int64_t x)
{
    void *array;
    array = (int64_t*) malloc(N * sizeof(int64_t));
    if (array == NULL) {
        fprintf(stderr, "Couldn't allocate memory for input array.\n");
    }
    int64_t *elt = array;
    cilk_for (uint32_t i = 0; i <= N-1; i++) {
        elt = (int64_t*) array + i;
        *elt = x;
    }
    free(array);
}

int64_t __attribute__ ((noinline)) sum_array_seq(uint32_t N, int64_t *array)
{
    int64_t sum = 0;
    int64_t *elt = array;
    for (uint32_t i = 0; i <= N-1; i++) {
        elt = (int64_t*) (array + i);
        sum += *elt;
    }
    return sum;
}
