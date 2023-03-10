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
        return test_main(argc-1, &argv[1]);
    } else {
        return bench_main(argc-1, &argv[1]);
    }
}

int test_main(int argc, char** argv)
{
    (void) argc;
    (void) argv;

    // Test slice functions.
    void *nums = (void*) fill_array_rand_seq(16);
    slice_t s0 = (slice_t) { nums, 16, sizeof(int64_t) };
    slice_print(&s0);

    // size_t len = slice_length(&s0);
    // slice_prod_t halves = slice_split_at(&s0, len / 2);
    // slice_print(&(halves.left));
    // slice_print(&(halves.right));

    void *sorted = mergesort(s0.base, s0.total_elems, s0.elt_size, compare_int64s);
    slice_t sorted_sl = (slice_t) {sorted, 16, sizeof(int64_t)};
    slice_print(&sorted_sl);

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
    } else if (prefix("sort", argv[1])) {
        b->tag = SORT;
        b->sort_setup = fill_array_rand_seq;
        b->sort_teardown = free;
        b->sort_run = insertionsort_glibc;
        b->sort_total_elems = total_elems;
        b->sort_size = sizeof(int64_t);
        b->sort_cmp = compare_int64s;
        if (strcmp(argv[1], "sort_insertion_glibc") == 0) {
            b->sort_run = insertionsort_glibc;
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
            total_elems = b->fa_total_elems;

            break;
        }

        case SUMARRAY: {
            // No setup required.
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
            total_elems = b->sa_total_elems;

            break;
        }

        case SORT: {
            // No setup required.
            int64_t *nums = (*(b->sort_setup))(b->sort_total_elems);
            int64_t *sorted;

            // Run the benchmark.
            for (size_t i = 0; i < NUM_ITERS; i++) {
                clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed);
                sorted = (*(b->sort_run))(nums, b->sort_total_elems, b->sort_size, b->sort_cmp);
                clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed);
                itertime = difftimespecs(&begin_timed, &end_timed);
                printf("itertime: %lf\n", itertime);
                batchtime += itertime;
            }

            // Teardown.
            (*(b->sort_teardown))(nums);
            (*(b->sort_teardown))(sorted);
            total_elems = b->sort_total_elems;

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
