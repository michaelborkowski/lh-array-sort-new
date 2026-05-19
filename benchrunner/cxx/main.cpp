#include "benchmarks.h"
#include "helpers.h"
#include "insertionsort.hpp"
#include "quicksort.hpp"
#include "mergesort.hpp"
#include <vector>

int main(int argc, char *argv[]) {

    int arr_size = atoi(argv[1]);
    int iters = atoi(argv[2]);

    int64_t *arr;
    std::chrono::time_point<std::chrono::system_clock> start, end;
    std::cout << "Benchmarking insertionsort inplace: " << std::endl;
    for (size_t i = 0; i < iters; i++) {
        arr = fill_array_rand_seq(arr_size);
        start = std::chrono::system_clock::now();
        insertionsort_inplace<int64_t>(arr, arr_size);
        end = std::chrono::system_clock::now();
        std::chrono::duration<double> elapsed_seconds = end - start;
        printf("itertime: %lf\n", elapsed_seconds.count());
        if (i < iters - 1) {
            delete[] arr;
        }
    }

    slice_assert_sorted(arr, arr_size);
    delete[] arr;

    std::cout << std::endl;
    std::cout << "Benchmarking quicksort inplace: " << std::endl;
    for (size_t i = 0; i < iters; i++) {
        arr = fill_array_rand_seq(arr_size);
        start = std::chrono::system_clock::now();
        quicksort_inplace<int64_t>(arr, arr_size);
        end = std::chrono::system_clock::now();
        std::chrono::duration<double> elapsed_seconds = end - start;
        printf("itertime: %lf\n", elapsed_seconds.count());
        if (i < iters - 1) {
            delete[] arr;
        }
    }

    slice_assert_sorted(arr, arr_size);
    delete[] arr;

    std::cout << std::endl;
    std::cout << "Benchmarking mergesort sequential: " << std::endl;
    for (size_t i = 0; i < iters; i++) {
        arr = fill_array_rand_seq(arr_size);
        std::vector<int64_t> work_buffer(arr_size);
        start = std::chrono::system_clock::now();
        bottomUpMergeSort<int64_t>(arr, work_buffer.data(), arr_size);
        end = std::chrono::system_clock::now();
        std::chrono::duration<double> elapsed_seconds = end - start;
        printf("itertime: %lf\n", elapsed_seconds.count());
        if (i < iters - 1) {
            delete[] arr;
        }
    }

    slice_assert_sorted(arr, arr_size);
    delete[] arr;

    return 0;
}
