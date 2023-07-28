#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>
#include <string.h>
#include <time.h>
#include <errno.h>

#include "benchmarks.h"
#include "helpers.h"
#include "cbench.h"

// -----------------------------------------------------------------------------

// Number of benchmark iterations.
const size_t NUM_ITERS = 10;

void simple_bench(const benchmark_t *b);
int test_main(int argc, char** argv);
int bench_main(int argc, char** argv);

int main(int argc, char** argv)
{
    if (strcmp(argv[1], "test") == 0) {
        return test_main(argc, argv);
    } else {
        return bench_main(argc, argv);
    }
}

int test_main(int argc, char** argv)
{
    (void) argc;
    (void) argv;

    // Test slice functions.
    size_t n = 10;
    void *nums = (void*) fill_array_rand_seq(n);
    slice_t s0 = (slice_t) { nums, n, sizeof(int64_t) };
    size_t len = slice_length(&s0);
    slice_prod_t halves = slice_split_at(&s0, len / 2);
    assert(slice_length(&(halves.left)) == 5);
    assert(slice_length(&(halves.right)) == 5);
    assert(compare_int64s(slice_nth(&(halves.left), 4), slice_nth(&s0, 4)) == 0);
    assert(compare_int64s(slice_nth(&(halves.right), 0), slice_nth(&s0, 5)) == 0);

    // Test sorting.
    size_t len2 = 8000000;
    void *nums2 = (void*) fill_array_rand_seq(len2);
    slice_t s2 = (slice_t) { nums2, len2, sizeof(int64_t) };
    void *sorted = mergesort_par(s2.base, s2.total_elems, s2.elt_size, compare_int64s);
    slice_t sorted_sl = (slice_t) {sorted, len2, sizeof(int64_t)};
    slice_assert_sorted(compare_int64s, &sorted_sl);

    return 0;
}

int bench_main(int argc, char** argv)
{
    if (argc < 2) {
        fprintf(stderr, "USAGE: ./cbench.exe BENCHMARK_NAME\n");
        exit(1);
    }

    size_t total_elems = 1000000;
    if (argc >= 3) {
        total_elems = atoll(argv[2]);
    }

    benchmark_t *b = malloc(sizeof(benchmark_t));

    if (prefix("fillarray", argv[1])) {
        printf("benchmarking C fill array.\n");
        b->tag = FILLARRAY;
        b->fa_teardown = free;
        b->fa_run = fill_array_seq;
        b->fa_total_elems = total_elems;
        b->fa_val = 12345;
        if (strcmp(argv[1], "fillarray_par") == 0) {
            b->fa_run = fill_array_par;
        }
    } else if (prefix("sumarray", argv[1])) {
        printf("benchmarking C sum array.\n");
        b->tag = SUMARRAY;
        b->sa_setup = fill_array_ones_seq;
        b->sa_teardown = free;
        b->sa_run = sum_array_seq;
        b->sa_total_elems = total_elems;
        if (strcmp(argv[1], "sumarray_par") == 0) {
            b->sa_run = sum_array_par;
        }
    } else if (prefix("copyarray", argv[1])) {
        printf("benchmarking C copy array.\n");
        size_t nbytes = total_elems * sizeof(int64_t);
        void *dst = malloc(nbytes);
        b->tag = COPYARRAY;
        b->cp_setup = fill_array_rand_seq;
        b->cp_teardown = free;
        b->cp_run = copy_seq;
        b->cp_dst = dst;
        b->cp_nbytes = nbytes;
        b->cp_total_elems = total_elems;
        if (strcmp(argv[1], "copyarray_par") == 0) {
            b->cp_run = copy_par;
        }
    } else if (prefix("fib", argv[1])) {
        printf("benchmarking fib\n");
        b->tag = FIB;
        b->fib_run = fib;
        b->fib_n = total_elems;
        if (strcmp(argv[1], "fib_par") == 0) {
            b->fib_run = fib_par;
        }
    } else if (prefix("sort", argv[1])) {
        b->tag = SORT;
        b->sort_setup = fill_array_rand_seq;
        b->sort_teardown = free;
        b->sort_run = insertionsort_glibc;
        b->sort_total_elems = total_elems;
        b->sort_elt_size = sizeof(int64_t);
        b->sort_cmp = compare_int64s;
        if (strcmp(argv[1], "sort_insertion_glibc") == 0) {
            b->sort_run = insertionsort_glibc;
        } else if (strcmp(argv[1], "sort_insertion") == 0) {
            b->sort_run = insertionsort;
        } else if (strcmp(argv[1], "sort_quick_glibc") == 0) {
            b->sort_run = quicksort_glibc;
        } else if (strcmp(argv[1], "sort_quick") == 0) {
            b->sort_run = quicksort;
        } else if (strcmp(argv[1], "sort_merge_seq") == 0) {
            b->sort_run = smergesort;
        } else if (strcmp(argv[1], "sort_merge_par") == 0) {
            b->sort_run = mergesort_par;
        } else if (strcmp(argv[1], "sort_cilk_seq") == 0) {
            b->sort_run = cilksort;
        } else if (strcmp(argv[1], "sort_cilk_par") == 0) {
            b->sort_run = cilksort_par;
        } else {
            fprintf(stderr, "Unknown benchmark: %s", argv[1]);
            exit(1);
        }
    } else {
        fprintf(stderr, "Unknown benchmark: %s", argv[1]);
        exit(1);
    }

    // Run the benchmark.
    simple_bench(b);

    return 0;
}

// Run a function N times and report mean/median.
void simple_bench(const benchmark_t *b)
{
    double batchtime = 0.0, itertime = 0.0;
    struct timespec begin_timed, end_timed;
    size_t total_elems;

    switch (b->tag) {
        case FILLARRAY: {
            total_elems = b->fa_total_elems;
            // No setup required.
            int64_t *ret;

            // Run the benchmark.
            for (size_t i = 0; i < NUM_ITERS; i++) {
                clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed);
                ret = (*(b->fa_run))(b->fa_total_elems, b->fa_val);
                clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed);
                itertime = difftimespecs(&begin_timed, &end_timed);
                printf("itertime: %lf\n", itertime);
                batchtime += itertime;
            }

            // Teardown.
            (*(b->fa_teardown))(ret);

            break;
        }

        case SUMARRAY: {
            total_elems = b->sa_total_elems;
            int64_t *nums = (*(b->sa_setup))(b->sa_total_elems);
            int64_t *ret_values = malloc(NUM_ITERS * sizeof(int64_t));
            int64_t ret;

            // Run the benchmark.
            for (size_t i = 0; i < NUM_ITERS; i++) {
                clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed);
                ret = (*(b->sa_run))(b->sa_total_elems, nums);
                clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed);
                *(int64_t*) (ret_values + (int64_t) i) = ret;
                itertime = difftimespecs(&begin_timed, &end_timed);
                printf("itertime: %lf\n", itertime);
                batchtime += itertime;
            }
            printf("SUM: %ld\n", ret_values[NUM_ITERS-1]);

            // Teardown.
            (*(b->sa_teardown))(nums);

            break;
        }

        case COPYARRAY: {
            total_elems = b->cp_total_elems;
            int64_t *nums = (*(b->cp_setup))(b->cp_total_elems);

            // Run the benchmark.
            for (size_t i = 0; i < NUM_ITERS; i++) {
                clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed);
                (*(b->cp_run))(b->cp_dst, nums, b->cp_nbytes);
                clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed);
                itertime = difftimespecs(&begin_timed, &end_timed);
                printf("itertime: %lf\n", itertime);
                batchtime += itertime;
            }

            // Teardown.
            (*(b->sa_teardown))(nums);

            break;
        }
        case FIB: {
            total_elems = b->fib_n;
            int64_t ret;
            // Run the benchmark.
            for (size_t i = 0; i < NUM_ITERS; i++) {
                clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed);
                ret = (*(b->fib_run))(b->fib_n);
                clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed);
                itertime = difftimespecs(&begin_timed, &end_timed);
                printf("itertime: %lf\n", itertime);
                batchtime += itertime;
            }
            printf("FIB: %ld\n", ret);
            break;
        }

        case SORT: {
            total_elems = b->sort_total_elems;
            int64_t *nums = (*(b->sort_setup))(b->sort_total_elems);
            int64_t *sorted;

            // Run the benchmark.
            for (size_t i = 0; i < NUM_ITERS; i++) {
                clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed);
                sorted = (*(b->sort_run))(nums, b->sort_total_elems, b->sort_elt_size, b->sort_cmp);
                clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed);
                itertime = difftimespecs(&begin_timed, &end_timed);
                printf("itertime: %lf\n", itertime);
                batchtime += itertime;
            }

            // Check if its sorted.
            slice_t sl = (slice_t) { sorted, b->sort_total_elems, b->sort_elt_size } ;
            slice_assert_sorted(b->sort_cmp, &sl);

            // Teardown.
            (*(b->sort_teardown))(nums);
            (*(b->sort_teardown))(sorted);

            break;
        }

        default: {
            fprintf(stderr, "Unknown benchmark tag: %d", b->tag);
            exit(1);
        }
    }

    printf("BENCHMARK: %s\n", benchmark_tag_str(b->tag));
    printf("TOTAL_ELEMS: %ld\n", total_elems);
    printf("ITERS: %ld\n", NUM_ITERS);
    printf("BATCHTIME: %e\n", batchtime);
    printf("SELFTIMED: %e\n", (batchtime / NUM_ITERS));
}
