#include "benchmarks.h"
#include "quicksort.cpp"

int64_t *quicksort_int(int64_t *pbase, size_t total_elems){
    return quicksort_inplace<int64_t>(pbase, total_elems);
}
