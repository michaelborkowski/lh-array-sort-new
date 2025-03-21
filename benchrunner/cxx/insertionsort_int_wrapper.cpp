#include "benchmarks.h"
#include "insertionsort.cpp"

extern "C" {
    extern int64_t *insertionsort_cxx_int(int64_t *pbase, size_t total_elems){
        return insertionsort_inplace<int64_t>(pbase, total_elems);
    }
}
