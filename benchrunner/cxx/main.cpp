#include <iostream>
#include "benchmarks.h"
#include "insertionsort.cpp"
#include "microbench.h"
#include "cbench.h"

int main() {

    int64_t *arr = fill_array_rand_seq(10000);
    int arr_size = 10000;

    int64_t *out = insertionsort_inplace<int64_t>(arr, arr_size);

    slice_assert_sorted_2(out, arr_size);

    return 0;
}
