#ifndef _CBENCH_H
#define _CBENCH_H

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <errno.h>
#include <time.h>

// -----------------------------------------------------------------------------

// Fill array function types, no setup required.
typedef int64_t* (*fillarray_run_fn_t) (size_t total_elems, int64_t val);
typedef void (*fillarray_teardown_fn_t) (void *array);

// Sum array function types.
typedef int64_t* (*sumarray_setup_fn_t) (size_t total_elems);
typedef int64_t (*sumarray_run_fn_t) (size_t total_elems, int64_t *nums);
typedef void (*sumarray_teardown_fn_t) (void *array);

// Copy array function types.
typedef int64_t* (*copyarray_setup_fn_t) (size_t total_elems);
typedef void (*copyarray_run_fn_t) (void *dst, void *src, size_t nbytes);
typedef void (*copyarray_teardown_fn_t) (void *array);

// Fib function types.
typedef int64_t (*fib_run_fn_t) (int64_t n);

// Copied from stdlib.h for reference.
typedef int (*__compar_fn_t) (const void *, const void *);

// Sort function types.
typedef void* (*sort_setup_fn_t) (size_t total_elems);
typedef void* (*sort_run_fn_t) (void *const pbase, size_t total_elems, size_t elt_size, __compar_fn_t cmp);
typedef void  (*sort_teardown_fn_t) (void *array);

// A tagged union that helps abstract over running different types of benchmarks.
enum benchmark_tag {
    SORT,
    FILLARRAY,
    SUMARRAY,
    COPYARRAY,
    FIB,
};

static inline char *benchmark_tag_str(enum benchmark_tag tag)
{
    switch (tag) {
        case SORT:
            return "SORT";
        case FILLARRAY:
            return "FILLARRAY";
        case SUMARRAY:
            return "SUMARRAY";
        case COPYARRAY:
            return "COPYARRAY";
        case FIB:
            return "FIB";
        default:
            return "UNKNOWN";
    }
}

typedef struct benchmark_t_ {
    enum benchmark_tag tag;

    union {
        // Fill array.
        struct {
            // No setup required. Teardown fn.
            fillarray_teardown_fn_t fa_teardown;
            // Function to benchmark.
            fillarray_run_fn_t fa_run;
            // Arguments to fn.
            size_t fa_total_elems;
            int64_t fa_val;
        };

        // Sum array.
        struct {
            // Setup and teardown.
            sumarray_setup_fn_t sa_setup;
            sumarray_teardown_fn_t sa_teardown;
            // Function to benchmark.
            sumarray_run_fn_t sa_run;
            // Arguments to fn.
            size_t sa_total_elems;
            // int64_t *sa_array;
        };

        // Copy array.
        struct {
            // Setup and teardown.
            copyarray_setup_fn_t cp_setup;
            copyarray_teardown_fn_t cp_teardown;
            // Function to benchmark.
            copyarray_run_fn_t cp_run;
            // Arguments to fn.
            void *cp_dst;
            size_t cp_nbytes;
            size_t cp_total_elems;
        };

        // Fibonacci.
        struct {
             fib_run_fn_t fib_run;
             int64_t fib_n;
        };

        // Sort function.
        struct {
            // Setup and teardown.
            sort_setup_fn_t sort_setup;
            sort_teardown_fn_t sort_teardown;
            // Function to benchmark.
            sort_run_fn_t sort_run;
            // Arguments to fn.
            // void *const sort_pbase;
            size_t sort_total_elems;
            size_t sort_elt_size;
            __compar_fn_t sort_cmp;
        };

    };
} benchmark_t;


#endif
