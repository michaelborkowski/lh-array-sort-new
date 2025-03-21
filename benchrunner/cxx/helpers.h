#ifndef _HELPERS_H
#define _HELPERS_H

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <errno.h>
#include <time.h>
#include <assert.h>

int64_t* __attribute__ ((noinline)) fill_array_rand_seq(size_t total_elems)
{
    void *nums;
    nums = (int64_t*) malloc(total_elems * sizeof(int64_t));
    if (nums == NULL) {
        fprintf(stderr, "Couldn't allocate memory for output array.\n");
        return NULL;
    }
    int64_t *elt = (int64_t *) nums;
    for (uint64_t i = 0; i <= total_elems-1; i++) {
        elt = (int64_t*) nums + i;
        *elt = rand();
    }
    return (int64_t *) nums;
}

static inline void slice_assert_sorted_2(int64_t *arr, int size)
{
    size_t len = size;
    int64_t a, b;
    for (size_t i = 0; i < len-1; i++) {
        a = arr[i];
        b = arr[i+1];
        if (a > b) {
            fprintf(stderr, "Elements at %zu and %zu are not sorted.", i, i+1);
            exit(1);
        }
    }
    printf("Sorted: OK\n");
}

#endif
