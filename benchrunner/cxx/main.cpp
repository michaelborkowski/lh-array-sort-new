#include "benchmarks.h"
#include "helpers.h"
#include "insertionsort.cpp"
#include "quicksort.cpp"
#include "mergesort.cpp"

int main(int argc, char *argv[]) {

    int arr_size = atoi(argv[1]);
    int iters = atoi(argv[2]);

    int64_t *out;
    std::chrono::time_point<std::chrono::system_clock> start, end;
    std::cout << "Benchmarking insertionsort inplace: " << std::endl;
    for (size_t i = 0; i < iters; i++) {
        int64_t *arr = fill_array_rand_seq(arr_size);
        start = std::chrono::system_clock::now();
        out = insertionsort_inplace<int64_t>(arr, arr_size);
        end = std::chrono::system_clock::now();
        std::chrono::duration<double> elapsed_seconds = end - start;
        printf("itertime: %lf\n", elapsed_seconds.count());
    }

    slice_assert_sorted_2(out, arr_size);

    std::cout << std::endl;
    std::cout << "Benchmarking quicksort inplace: " << std::endl;
    for (size_t i = 0; i < iters; i++) {
        int64_t *arr = fill_array_rand_seq(arr_size);
        start = std::chrono::system_clock::now();
        out = quicksort_inplace<int64_t>(arr, arr_size);
        end = std::chrono::system_clock::now();
        std::chrono::duration<double> elapsed_seconds = end - start;
        printf("itertime: %lf\n", elapsed_seconds.count());
    }

    slice_assert_sorted_2(out, arr_size);

    std::cout << std::endl;
    std::cout << "Benchmarking mergesort sequential: " << std::endl;
    for (size_t i = 0; i < iters; i++) {
        int64_t *arr = fill_array_rand_seq(arr_size);
        int64_t *copyOut = new int64_t[arr_size];
        copyArray<int64_t>(arr, copyOut, arr_size);
        start = std::chrono::system_clock::now();
        out = bottomUpMergeSort<int64_t>(arr, copyOut, arr_size);
        end = std::chrono::system_clock::now();
        std::chrono::duration<double> elapsed_seconds = end - start;
        printf("itertime: %lf\n", elapsed_seconds.count());
    }

    slice_assert_sorted_2(out, arr_size);

    return 0;
}
