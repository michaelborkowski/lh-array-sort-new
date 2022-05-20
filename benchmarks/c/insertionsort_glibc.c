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


#include "cbench.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

void *insertionsort_glibc (void *const pbase, size_t total_elems, size_t size,
                    __compar_fn_t cmp)
{
    char *base_ptr = (char *) pbase;
    char *const end_ptr1 = &base_ptr[size * (total_elems - 1)];
    char *run_ptr;

    // copy into a fresh array.
    run_ptr = base_ptr;
    char *alloc_ptr = malloc(total_elems * size);
    if (alloc_ptr == NULL) {
        fprintf(stderr, "insertionsort: couldn't allocate");
        exit(1);
    }
    memcpy(alloc_ptr, run_ptr, (size * total_elems));

    // sort.
    base_ptr = alloc_ptr;
    char *const end_ptr = &base_ptr[size * (total_elems - 1)];
    char *tmp_ptr = base_ptr;
    // run_ptr = base_ptr + size;
    run_ptr = base_ptr;
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
    return (void *) alloc_ptr;
}
