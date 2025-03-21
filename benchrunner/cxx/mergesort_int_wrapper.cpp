#include "benchmarks.h"
#include "mergesort.cpp"


int64_t *bottom_up_merge_sort_int(int64_t *pbase, size_t total_elems){

    int64_t *copy_pbase = new int64_t[total_elems];
    copyArray<int64_t>(pbase, copy_pbase, total_elems);
    return bottomUpMergeSort<int64_t>(pbase, copy_pbase, total_elems);
}
