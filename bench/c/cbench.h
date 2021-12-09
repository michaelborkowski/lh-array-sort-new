#ifndef _CBENCH_H
#define _CBENCH_H

#include <stdlib.h>

// // Copied from stdlib.h for readability.
// typedef int (*__compar_fn_t) (const void *, const void *);

typedef void (*sort_fn_t) (void *const pbase, size_t total_elems, size_t size,
                           __compar_fn_t cmp);

void quicksort_glibc (void *const pbase, size_t total_elems, size_t size,
                      __compar_fn_t cmp);

void insertionsort (void *const pbase, size_t total_elems, size_t size,
                    __compar_fn_t cmp);

#endif
