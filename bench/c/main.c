#include "cbench.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <string.h>
#include <time.h>
#include <errno.h>

int compare_int64s(const void* a, const void* b)
{
    uint64_t arg1 = *(const uint64_t*)a;
    uint64_t arg2 = *(const uint64_t*)b;

    if (arg1 < arg2) return -1;
    if (arg1 > arg2) return 1;
    return 0;

    // return (arg1 > arg2) - (arg1 < arg2); // possible shortcut
    // return arg1 - arg2; // erroneous shortcut (fails if INT_MIN is present)
}

int compare_doubles(const void* a, const void* b)
{
    double arg1 = *(const double*)a;
    double arg2 = *(const double*)b;

    if (arg1 < arg2) return -1;
    if (arg1 > arg2) return 1;
    return 0;

    // return (arg1 > arg2) - (arg1 < arg2); // possible shortcut
    // return arg1 - arg2; // erroneous shortcut (fails if INT_MIN is present)
}

int bench_sort1(int argc, char** argv)
{
    char *algo = argv[1];
    char *elt_type = argv[2];
    uint32_t N = atoi(argv[3]);

    // Sorting params.
    void *array;
    size_t elt_size;
    __compar_fn_t cmp_fn;
    sort_fn_t sort_fn;

    if (strcmp(algo,"insertion") == 0) {
        sort_fn = insertionsort;
    }

    if (strcmp(elt_type,"int64") == 0) {
        // Set params.
        array = (uint64_t*) malloc(N * sizeof(uint64_t));
        if (array == NULL) {
            fprintf(stderr, "Couldn't allocate memory for input array.\n");
        }
        elt_size = sizeof(int);
        cmp_fn = compare_int64s;
        // Initialize input.
        srand(time(NULL));
        uint64_t *elt = array;
        for (uint32_t i = 0; i <= N-1; i++) {
            elt = (uint64_t*) array + i;
            *elt = rand();
        }
    } else {
        fprintf(stderr, "Unknown type: %s\n", elt_type);
        exit(1);
    }

    // Start protocol for criterion-interactive.
    printf("READY\n");
    fflush(stdout);

    char *criterion_cmd = (char*) malloc(100);
    ssize_t read;
    size_t len;
    uint32_t rounds;
    uint32_t i;

    // Wait for criterion-interactive to send a command.
    read = getline(&criterion_cmd, &len, stdin);
    while (strcmp(criterion_cmd,"EXIT") != 0) {
        if (read == -1) {
            printf("Couldn't read from stdin, error=%d\n", errno);
            exit(1);
        }

        // One round of benchmarking.
        if (strncmp(criterion_cmd,"START_BENCH", 11) == 0) {
            rounds = atol(criterion_cmd+12);

#ifdef CBENCH_DEBUG
            puts(criterion_cmd);
            printf("rounds=%" PRIu32 "\n", rounds);
#endif

            // The main event.
            for (i = 0; i <= rounds; i++)
                (*sort_fn)(array, N, elt_size, cmp_fn);

            printf("END_BENCH\n");
            fflush(stdout);
        }

        // Prepare for next round.
        rounds=0;
        read = getline(&criterion_cmd, &len, stdin);
    }

    free(criterion_cmd);
    free(array);

    return 0;
}

double gib_difftimespecs(struct timespec* t0, struct timespec* t1)
{
    return (double)(t1->tv_sec - t0->tv_sec)
            + ((double)(t1->tv_nsec - t0->tv_nsec) / 1000000000.0);
}

void print_usage_and_exit(void)
{
    printf("Usage: cbench.exe ARRAY_SIZE ITERS\n");
    exit(1);
}

int bench_sort2(int argc, char** argv)
{
    if (argc < 3) {
        print_usage_and_exit();
    }

    int N = atol(argv[1]);
    int rounds = atol(argv[2]);

    int *array = malloc(N * sizeof(int));
    for (int i = 0; i <= N-1; i++) {
        array[i] = rand();
    }

    struct timespec begin_timed;
    struct timespec end_timed;
    double round_timings[rounds];
    double round_time;
    int j = 0;

    for (int i = 0; i < rounds; i++) {
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed);
        insertionsort(array, N, sizeof(int), compare_int64s);
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed);
        round_time = gib_difftimespecs(&begin_timed, &end_timed);
        round_timings[j] = round_time;
        printf("iter time: %e\n", round_time);
        j++;
    }
    qsort(round_timings, 9, sizeof(double), compare_doubles);
    printf("median time: %e\n", round_timings[(rounds/2)+1]);
    return 0;
}

int main(int argc, char** argv)
{
    // bench_sort1(argc,argv);
    bench_sort2(argc,argv);
    return 0;
}
