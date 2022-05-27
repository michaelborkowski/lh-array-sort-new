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
    int64_t arg1 = *(const int64_t*)a;
    int64_t arg2 = *(const int64_t*)b;

    if (arg1 < arg2) return -1;
    if (arg1 > arg2) return 1;
    return 0;
}

int compare_ints(const void* a, const void* b)
{
    int arg1 = *(const int*)a;
    int arg2 = *(const int*)b;

    if (arg1 < arg2) return -1;
    if (arg1 > arg2) return 1;
    return 0;
}

int compare_doubles(const void* a, const void* b)
{
    double arg1 = *(const double*)a;
    double arg2 = *(const double*)b;

    if (arg1 < arg2) return -1;
    if (arg1 > arg2) return 1;
    return 0;
}

int bench_insertion_glibc(int argc, char** argv)
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
        sort_fn = insertionsort_glibc;
    }

    if (strcmp(elt_type,"int64") == 0) {
        // Set params.
        array = (int64_t*) malloc(N * sizeof(int64_t));
        if (array == NULL) {
            fprintf(stderr, "Couldn't allocate memory for input array.\n");
        }
        elt_size = sizeof(int64_t);
        cmp_fn = compare_int64s;
        // Initialize input.
        srand(time(NULL));
        int64_t *elt = array;
        for (uint32_t i = 0; i <= N-1; i++) {
            elt = (int64_t*) array + i;
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

    void *sorted;

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
            for (i = 0; i <= rounds; i++) {
                (*sort_fn)(array, N, elt_size, cmp_fn);
            }

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

// cilksort.c contains a function called fill_sort...
int __attribute__ ((noinline)) fill_array2(uint32_t N, int64_t x)
{
    void *array;
    array = (int64_t*) malloc(N * sizeof(int64_t));
    if (array == NULL) {
        fprintf(stderr, "Couldn't allocate memory for input array.\n");
    }
    int64_t *elt = array;
    for (uint32_t i = 0; i <= N-1; i++) {
        elt = (int64_t*) array + i;
        *elt = x;
    }
    free(array);
}

int bench_fill_array(int argc, char** argv)
{
    char *algo = argv[1];
    char *elt_type = argv[2];
    uint32_t N = atoi(argv[3]);

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
            for (i = 0; i <= rounds; i++) {
                fill_array2(N, 1000);
            }

            printf("END_BENCH\n");
            fflush(stdout);
        }

        // Prepare for next round.
        rounds=0;
        read = getline(&criterion_cmd, &len, stdin);
    }

    free(criterion_cmd);

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

int bench_gibbon_insertion1(int argc, char** argv);
int bench_gibbon_insertion2(int argc, char** argv);

int main(int argc, char** argv)
{
    printf("benchmarking fill array:\n");
    bench_fill_array(argc,argv);

    // printf("benchmarking glibc insertion sort:\n");
    // bench_insertion_glibc(argc,argv);

    // printf("gibbon (1):\n");
    // bench_gibbon_insertion1(argc,argv);

    // printf("gibbon (2):\n");
    // bench_gibbon_insertion2(argc,argv);

    return 0;
}
