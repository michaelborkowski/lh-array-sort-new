#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <iostream>
#include "helpers.h"

// -----------------------------------------------------------------------------

template<typename T> T *insertionsort_inplace(T *pbase, size_t total_elems);
void insertionsort_inplace_cmp(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp);


// void *insertionsort_copy(void *const pbase, size_t total_elems, size_t size)
// {
//     // Copy into a fresh array.
//     char *cpy = (char*) malloc(total_elems * size);
//     if (cpy == NULL) {
//         fprintf(stderr, "insertionsort: couldn't allocate");
//         exit(1);
//     }
//     our_memcpy(cpy, (char *) pbase, (size * total_elems));
//
//     // Sort "cpy" in place.
//     insertionsort_inplace(cpy, total_elems, size);
//     return cpy;
// }


// void *insertionsort_cmp(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp)
// {
//     // Copy into a fresh array.
//     char *cpy = (char*) malloc(total_elems * size);
//     if (cpy == NULL) {
//         fprintf(stderr, "insertionsort: couldn't allocate");
//         exit(1);
//     }
//     our_memcpy(cpy, (char *) pbase, (size * total_elems));
//
//     // Sort "cpy" in place.
//     insertionsort_inplace_cmp(cpy, total_elems, size, cmp);
//     return cpy;
// }

/*
    i ← 1
    while i < n
        temp ← array[i]
        j ← i
        while j > 0 and array[j - 1] > temp
            array[j] ← array[j - 1]
            j ← j - 1
        end while
        array[j] ← temp
        i ← i + 1
    end while
*/
// void insertionsort_inplace_cmp(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp)
// {
//     char *const base_ptr = (char *) pbase;
//     char *const end_ptr = &base_ptr[size * (total_elems - 1)];
//     char *run_ptr = base_ptr + size;
//     char *tmp_ptr;
//
//     void *temp = malloc(size);
//     while (run_ptr <= end_ptr) {
//         memcpy(temp, run_ptr, size);
//         tmp_ptr = run_ptr;
//         while (tmp_ptr > base_ptr && (*cmp)((tmp_ptr - size), temp) > 0) {
//             memcpy(tmp_ptr, (tmp_ptr - size), size);
//             tmp_ptr -= size;
//         }
//         memcpy(tmp_ptr, temp, size);
//         run_ptr += size;
//     }
//     return;
// }


//     i ← 1
//     while i < n
//         temp ← array[i]
//         j ← i
//         while j > 0 and array[j - 1] > temp
//             array[j] ← array[j - 1]
//             j ← j - 1
//         end while
//         array[j] ← temp
//         i ← i + 1
//     end while

template<typename T>
T *insertionsort_inplace(T *pbase, size_t total_elems)
{
    int i = 0;
    while (i < total_elems){
        T temp = pbase[i];
        int j = i;
        while(j > 0 && pbase[j - 1] > temp){
            pbase[j] = pbase[j-1];
            j = j - 1;
        }
        pbase[j] = temp;
        i = i + 1;
    }

    return pbase;
}
