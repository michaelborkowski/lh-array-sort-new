// Monomorphic port of insertionsort_inplace from csorts/insertionsort.c.
// Changes from the generic: int64_t* instead of void*/char* + size_t size,
// direct int64_t assignment instead of memcpy, stack variable instead of
// malloc'd temp buffer.
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

int64_t *insertionsort_mono_inplace(int64_t *arr, size_t n)
{
    int64_t *const end_ptr = arr + (n - 1);
    int64_t *run_ptr = arr + 1;
    int64_t *tmp_ptr;
    int64_t temp;

    while (run_ptr <= end_ptr) {
        temp    = *run_ptr;
        tmp_ptr = run_ptr;
        while ((tmp_ptr > arr) && (*(tmp_ptr - 1) > temp)) {
            *tmp_ptr = *(tmp_ptr - 1);
            tmp_ptr--;
        }
        *tmp_ptr = temp;
        run_ptr++;
    }
    return arr;
}
