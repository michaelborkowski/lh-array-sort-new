/* Copyright (C) 1991-2021 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <https://www.gnu.org/licenses/>.  */


#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include "helpers.h"

// -----------------------------------------------------------------------------

void insertionsort_glibc_inplace(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp);

void *insertionsort_glibc(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp)
{
    // Copy into a fresh array.
    char *cpy = (char *) malloc(total_elems * size);
    if (cpy == NULL) {
        fprintf(stderr, "insertionsort: couldn't allocate");
        exit(1);
    }
    our_memcpy(cpy, (char *) pbase, (size * total_elems));

    // Sort "cpy" in place.
    insertionsort_glibc_inplace(cpy, total_elems, size, cmp);
    return cpy;
}

/* Byte-wise swap two items of size SIZE. */
#define SWAP(a, b, size)						      \
  do									      \
    {									      \
      size_t __size = (size);						      \
      char *__a = (a), *__b = (b);					      \
      do								      \
        {								      \
          char __tmp = *__a;						      \
          *__a++ = *__b;						      \
          *__b++ = __tmp;						      \
        } while (--__size > 0);						      \
    } while (0)

#define MAX_THRESH 4

#define min(x, y) ((x) < (y) ? (x) : (y))

void insertionsort_glibc_inplace(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp)
{
    const size_t max_thresh = MAX_THRESH * size;
    char *base_ptr = (char *) pbase;
    char *const end_ptr = &base_ptr[size * (total_elems - 1)];
    char *tmp_ptr = base_ptr;
    char *thresh = min(end_ptr, base_ptr + max_thresh);
    char *run_ptr;

    /* Find smallest element in first threshold and place it at the
       array's beginning.  This is the smallest array element,
       and the operation speeds up insertion sort's inner loop. */

    for (run_ptr = tmp_ptr + size; run_ptr <= thresh; run_ptr += size) {
        if ((*cmp) ((void *) run_ptr, (void *) tmp_ptr) < 0) {
            tmp_ptr = run_ptr;
        }
    }

    if (tmp_ptr != base_ptr) {
        SWAP (tmp_ptr, base_ptr, size);
    }

    /* Insertion sort, running from left-hand-side up to right-hand-side.  */
    run_ptr = base_ptr + size;

    // Sort.
    while ((run_ptr += size) <= end_ptr) {
        tmp_ptr = run_ptr - size;
        while ((*cmp) ((void *) run_ptr, (void *) tmp_ptr) < 0)
            tmp_ptr -= size;
        tmp_ptr += size;
        if (tmp_ptr != run_ptr) {
            char *trav;
            trav = run_ptr + size;
            while (--trav >= run_ptr) {
                char c = *trav;
                char *hi, *lo;
                for (hi = lo = trav; (lo -= size) >= tmp_ptr; hi = lo)
                    *hi = *lo;
                *hi = c;
            }
        }
    }

    return;
}
