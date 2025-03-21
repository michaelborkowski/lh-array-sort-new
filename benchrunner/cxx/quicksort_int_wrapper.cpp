#include "benchmarks.h"
#include "quicksort.cpp"

extern "C" {
    extern int64_t *quicksort_cxx_int(int64_t *pbase, size_t total_elems){
        return quicksort_inplace<int64_t>(pbase, total_elems);
    }
}
