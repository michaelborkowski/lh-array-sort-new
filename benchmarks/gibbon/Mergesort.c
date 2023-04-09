#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>
#include <alloca.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
// #include <sys/sysinfo.h>
#ifdef _WIN64
#include <windows.h>
#endif
#include <unistd.h>
#include <fcntl.h>
#include <stdarg.h> // For va_start etc
#include <errno.h>
//#include <utlist.h>
//#include <uthash.h>
//#include <utarray.h>
#ifdef _POINTER
#include <gc.h>
#endif

#include <cilk/cilk.h>
#include <cilk/cilk_api.h>


#define KB 1024lu
#define MB (KB * 1000lu)
#define GB (MB * 1000lu)

#define REDIRECTION_TAG 255
#define INDIRECTION_TAG 254

// Initial size of BigInfinite buffers
static long long global_init_biginf_buf_size = (4 * GB);

// Initial size of Infinite buffers
static long long global_init_inf_buf_size = 1 * KB;

// Maximum size of a chunk, see GitHub #110.
static long long global_inf_buf_max_chunk_size = 1 * GB;

static long long global_size_param = 1;
static long long global_iters_param = 1;

static char* global_benchfile_param = NULL;
static char* global_arrayfile_param = NULL;
// Number of lines in the arrayfile
static long long global_arrayfile_length_param = -1;

// Sequential for now:
static const int num_workers = 1;

// Count the number of regions allocated.
static long long global_region_count = 0;
static bool global_region_count_flag = false;

#ifdef _PARALLEL
static inline void bump_global_region_count() {
    __atomic_add_fetch(&global_region_count, 1, __ATOMIC_SEQ_CST);
    return;
}
#else
static inline void bump_global_region_count() {
    global_region_count++;
    return;
}
#endif

static inline void print_global_region_count() {
    printf("REGION_COUNT: %lld\n", global_region_count);
    return;
}

#define REDIRECTION_NODE_SIZE 9
#define MAX(a,b) (((a)>(b))?(a):(b))
#define MIN(a,b) (((a)<(b))?(a):(b))

// https://www.cprogramming.com/snippets/source-code/find-the-number-of-cpu-cores-for-windows-mac-or-linux
static int get_num_processors() {
#ifdef _WIN64
    SYSTEM_INFO sysinfo;
    GetSystemInfo(&sysinfo);
    return sysinfo.dwNumberOfProcessors;
#else
    return sysconf(_SC_NPROCESSORS_ONLN);
#endif
}

// Requires -std=gnu11
int dbgprintf(const char *format, ...) {
    int code = 0;
    va_list args;
    va_start(args, format);
#ifdef _DEBUG
    code = vprintf(format, args);
#endif
    va_end(args);
    return code;
}


// -----------------------------------------------------------------------------
// Allocators
// -----------------------------------------------------------------------------


// -------------------------------------
// Bump allocation for linked-lists
// -------------------------------------


#ifdef _BUMPALLOC
// #define _DEBUG
#warning "Using bump allocator."

__thread char* bumpalloc_heap_ptr = (char*)NULL;
__thread char* bumpalloc_heap_ptr_end = (char*)NULL;

char* saved_heap_ptr_stack[100];
int num_saved_heap_ptr = 0;

// For simplicity just use a single large slab:
static inline void INITBUMPALLOC() {
      bumpalloc_heap_ptr = (char*)malloc(global_init_biginf_buf_size);
      bumpalloc_heap_ptr_end = bumpalloc_heap_ptr + global_init_biginf_buf_size;
#ifdef _DEBUG
      printf("Arena size for bump alloc: %lld\n", global_init_biginf_buf_size);
      printf("BUMPALLOC/INITBUMPALLOC DONE: heap_ptr = %p\n", bumpalloc_heap_ptr);
#endif
}

static inline void* BUMPALLOC(long long n) {
      if (! bumpalloc_heap_ptr) {
          INITBUMPALLOC();
      }
      if (bumpalloc_heap_ptr + n < bumpalloc_heap_ptr_end) {
          char* old= bumpalloc_heap_ptr;
          bumpalloc_heap_ptr += n;
          return old;
      } else {
          fprintf(stderr, "Warning: bump allocator ran out of memory.");
          exit(1);
      }
}

// Snapshot the current heap pointer value across all threads.
void save_alloc_state() {
  dbgprintf("Saving(%p): pos %d", heap_ptr, num_saved_heap_ptr);
  saved_heap_ptr_stack[num_saved_heap_ptr] = heap_ptr;
  num_saved_heap_ptr++;
  dbgprintf("\n");
}

void restore_alloc_state() {
  if(num_saved_heap_ptr <= 0) {
    fprintf(stderr, "Bad call to restore_alloc_state!  Saved stack empty!\ne");
    exit(1);
  }
  num_saved_heap_ptr--;
  dbgprintf("Restoring(%p): pos %d, discarding %p",
            saved_heap_ptr_stack[num_saved_heap_ptr], num_saved_heap_ptr, bumpalloc_heap_ptr);
  bumpalloc_heap_ptr = saved_heap_ptr_stack[num_saved_heap_ptr];
}


#else
// Regular malloc mode:
void INITBUMPALLOC() {}
void save_alloc_state() {}
void restore_alloc_state() {}

#define BUMPALLOC(n) malloc(n)

#endif // BUMPALLOC


// -------------------------------------
// ALLOC and ALLOC_PACKED macros
// -------------------------------------


/*

If parallelism is enabled, we always use a malloc based allocator
since Boehm GC is not thread-safe in its default configuration. It can be
made thread-safe by building it with appropriate flags, but we don't do that.
Presently, all parallel pointer-based programs will leak memory.

*/

#ifdef _PARALLEL
#define ALLOC(n) malloc(n)
#define ALLOC_PACKED_BIG(n) malloc(n)
char *ALLOC_COUNTED(size_t size) {
    bump_global_region_count();
    return ALLOC(size);
}
#else
  #ifdef _POINTER
#define ALLOC(n) GC_MALLOC(n)
#define ALLOC_PACKED_BIG(n) GC_MALLOC(n)
char *ALLOC_COUNTED(size_t size) {
    bump_global_region_count();
    return GC_MALLOC(size);
}
  #else
#define ALLOC(n) malloc(n)
#define ALLOC_PACKED_BIG(n) malloc(n)
char *ALLOC_COUNTED(size_t size) {
    bump_global_region_count();
    return ALLOC(size);
}
  #endif // _POINTER
#endif // _PARALLEL


// Could try alloca() here.  Better yet, we could keep our own,
// separate stack and insert our own code to restore the pointer
// before any function that (may have) called ALLOC_SCOPED returns.

// #define ALLOC_SCOPED() alloca(1024)
#define ALLOC_SCOPED(n) alloca(n)
// #define ALLOC_SCOPED() alloc_scoped()

// Stack allocation is either too small or blows our stack.
// We need a way to make a giant stack if we want to use alloca.
// #define ALLOC_SCOPED() ALLOC(global_init_biginf_buf_size)

// Our global pointer.  No parallelism.
// static char* stack_scoped_region;
// char* alloc_scoped() { return stack_scoped_region; }



// -------------------------------------
// Basic types
// -------------------------------------

// Must be consistent with sizeOfTy defined in Gibbon.Language.Syntax.

typedef unsigned char TagTyPacked;
typedef unsigned char TagTyBoxed;
typedef long long IntTy;
typedef char CharTy;
typedef float FloatTy;
typedef unsigned long long SymTy;
typedef bool BoolTy;
typedef char* PtrTy;
typedef char* CursorTy;


// -------------------------------------
// Helpers
// -------------------------------------

char* read_benchfile_param() {
  if (global_benchfile_param == NULL) {
    fprintf(stderr, "read_benchfile_param: benchmark input file was not set! Set using --bench-input.\n");
    exit(1);
  } else
    return global_benchfile_param;
}

char* read_arrayfile_param() {
  if (global_arrayfile_param == NULL) {
    fprintf(stderr, "read_arrayfile_param: array input file was not set! Set using --array-input.\n");
    exit(1);
  } else
    return global_arrayfile_param;
}

IntTy read_arrayfile_length_param() {
  if (global_arrayfile_length_param == -1) {
    fprintf(stderr, "read_arrayfile_length_param: array input file length was not set! Set using --array-input-length.\n");
    exit(1);
  } else
    return global_arrayfile_length_param;
}


// fun fact: __ prefix is actually reserved and this is an undefined behavior.
// These functions must be provided by the code generator.
int __main_expr();


void show_usage(char** argv)
{
    printf("\n");
    printf("This binary was generated by the Gibbon compiler.\n");
    printf("\n");
    printf("Usage: %s [OPTS] [size] [iters]\n", argv[0]);

    printf("\n");
    printf("Options:\n");
    printf(" --buffer-size <bytes>      Set the buffer size (default %lld).\n", global_init_biginf_buf_size);
    printf(" --bench-input <path>       Set the input file read for benchmarking. Applies only\n");
    printf("                            IF the program was *compiled* with --bench-fun. \n");
    return;
}

double avg(const double* arr, int n)
{
    double sum = 0.0;
    for(int i=0; i<n; i++) sum += arr[i];
    return sum / (double)n;
}

double difftimespecs(struct timespec* t0, struct timespec* t1)
{
    return (double)(t1->tv_sec - t0->tv_sec)
      + ((double)(t1->tv_nsec - t0->tv_nsec) / 1000000000.0);
}

int compare_doubles(const void *a, const void *b)
{
    const double *da = (const double *) a;
    const double *db = (const double *) b;
    return (*da > *db) - (*da < *db);
}

// Exponentiation
IntTy expll(IntTy base, IntTy pow) {
    if (base == 2) {
        return (1 << pow);
    } else {
        IntTy i, result = 1;
        for (i = 0; i < pow; i++)
            result *= base;
        return result;
    }
 }

// -------------------------------------
// Symbol table
// -------------------------------------

#define global_max_symbol_len 256

// Invariant: should always be equal to max(sym_table_keys)
static SymTy global_gensym_counter = 0;

// Its value is updated by the flags parser.
static char *global_bench_prog_param;


// -------------------------------------
// Vectors
// -------------------------------------

typedef struct VectorTy_struct {
    // Bounds on the vector.
    IntTy vec_lower, vec_upper;

    // Size of each element.
    IntTy vec_elt_size;

    // Actual elements of the vector.
    void* vec_data;
} VectorTy;

VectorTy* vector_alloc(IntTy num, IntTy elt_size) {
    VectorTy *vec = ALLOC(sizeof(VectorTy));
    if (vec == NULL) {
        printf("alloc_vector: malloc failed: %ld", sizeof(VectorTy));
        exit(1);
    }
    void* data = ALLOC(num * elt_size);
    if (data == NULL) {
        printf("alloc_vector: malloc failed: %ld", sizeof(num * elt_size));
        exit(1);
    }
    vec->vec_lower = 0;
    vec->vec_upper = num;
    vec->vec_elt_size = elt_size;
    vec->vec_data = data;
    return vec;
}

IntTy vector_length(VectorTy *vec) {
    return (vec->vec_upper - vec->vec_lower);
}

BoolTy vector_is_empty(VectorTy *vec) {
    return (vector_length(vec) == 0);
}

VectorTy* vector_slice(IntTy i, IntTy n, VectorTy *vec) {
    IntTy lower = vec->vec_lower + i;
    IntTy upper = vec->vec_lower + i + n;
    if ((lower > vec->vec_upper)) {
        printf("vector_slice: lower out of bounds, %lld > %lld", lower, vec->vec_upper);
        exit(1);
    }
    if ((upper > vec->vec_upper)) {
        printf("vector_slice: upper out of bounds: %lld > %lld", upper, vec->vec_upper);
        exit(1);
    }
    VectorTy *vec2 = ALLOC(sizeof(VectorTy));
    if (vec == NULL) {
        printf("vector_slice: malloc failed: %ld", sizeof(VectorTy));
        exit(1);
    }
    vec2->vec_lower = lower;
    vec2->vec_upper = upper;
    vec2->vec_elt_size = vec->vec_elt_size;
    vec2->vec_data = vec->vec_data;
    return vec2;
}

// The callers must cast the return value.
static inline void* vector_nth(VectorTy *vec, IntTy i) {
    // if (i < vec->lower || i > vec->upper) {
    //     printf("vector_nth index out of bounds: %lld (%lld,%lld) \n", i, vec->vec_lower, vec->vec_upper);
    //     exit(1);
    // }
    return (vec->vec_data + (vec->vec_elt_size * (vec->vec_lower + i)));
}

static inline VectorTy* vector_inplace_update(VectorTy *vec, IntTy i, void* elt) {
    void* dst = vector_nth(vec, i);
    memcpy(dst, elt, vec->vec_elt_size);
    return vec;
}

static inline VectorTy* vector_copy(VectorTy *vec) {
    IntTy len = vector_length(vec);
    void *start = vector_nth(vec, 0);
    VectorTy *vec2 = vector_alloc(len, vec->vec_elt_size);
    memcpy(vec2->vec_data, start, len * vec->vec_elt_size);
    return vec2;
}

static inline VectorTy* vector_inplace_sort(VectorTy *vec, int (*compar)(const void *, const void*)) {
    void *start = vector_nth(vec, 0);
    qsort(start, vector_length(vec), vec->vec_elt_size, compar);
    return vec;
}

static inline VectorTy* vector_sort(VectorTy *vec, int (*compar)(const void *, const void*)) {
    VectorTy *vec2 = vector_copy(vec);
    vector_inplace_sort(vec2, compar);
    return vec2;
}

static inline VectorTy* vector_concat(VectorTy *vec) {
    // Length of the input vector.
    IntTy len = vector_length(vec);
    // Length of the concatenated vector.
    IntTy result_len = 0;
    // Size of each element in the concatenated vector.
    IntTy result_elt_size = 0;
    VectorTy **elt_ref, *elt;
    for (IntTy i = 0; i < len; i++) {
        elt_ref = vector_nth(vec, i);
        elt = *elt_ref;
        result_elt_size = elt->vec_elt_size;
        result_len += vector_length(elt);
    }

    // Concatenated vector.
    VectorTy *result = vector_alloc(result_len, result_elt_size);
    IntTy elt_len;
    // A counter that tracks the index of elements in 'result'.
    IntTy k = 0;
    for (IntTy i = 0; i < len; i++) {
        elt_ref = vector_nth(vec, i);
        elt = *elt_ref;
        elt_len = vector_length(elt);

        for (IntTy j = 0; j < elt_len; j++) {
            void* k_elt = vector_nth(elt, j);
            vector_inplace_update(result, k, k_elt);
            k++;
        }
    }

    return result;
}

static inline void vector_free(VectorTy *vec) {
    free(vec->vec_data);
    free(vec);
    return;
}

static inline VectorTy* vector_merge(VectorTy *vec1, VectorTy *vec2) {
    if (vec1->vec_upper != vec2->vec_lower) {
        printf("vector_merge: non-contiguous slices, (%lld,%lld), (%lld,%lld).",
               vec1->vec_lower, vec1->vec_upper, vec2->vec_lower, vec2->vec_upper);
        exit(1);
    }
    VectorTy *merged = ALLOC(sizeof(VectorTy));
    if (merged == NULL) {
        printf("vector_merge: malloc failed: %ld", sizeof(VectorTy));
        exit(1);
    }
    merged->vec_lower = vec1->vec_lower;
    merged->vec_upper = vec2->vec_upper;
    merged->vec_elt_size = vec1->vec_elt_size;
    merged->vec_data = vec1->vec_data;
    return merged;
}

void print_timing_array(VectorTy *times) {
    printf("TIMES: [");
    double *d;
    IntTy n = vector_length(times);
    for(int i = 0; i < n; i++) {
        d = vector_nth(times, i);
        if (i == (n-1)) {
            printf("%f",*d);
        }
        else {
            printf("%f, ",*d);
        }
    }
    printf("]\n");
}

double sum_timing_array(VectorTy *times) {
    double *d;
    double acc = 0;
    for(int i = 0; i < vector_length(times); i++) {
        d = vector_nth(times, i);
        acc += *d;
    }
    return acc;
}

/* -------------------------------------------------------------------------------- */

int main(int argc, char** argv)
{
    // parameters to parse:
    //
    //   num iterations: How many times to repeat a benchmark.
    //   tree size: An integer passes to `build_tree()`.

    struct rlimit lim;
    int code;
    if ( (code = getrlimit(RLIMIT_STACK, &lim)) ) {
      fprintf(stderr, " [gibbon rts] failed to getrlimit, code %d\n", code);
      exit(1);
    }

    // lim.rlim_cur = 1024LU * 1024LU * 1024LU; // 1GB stack.
    lim.rlim_cur = 512LU * 1024LU * 1024LU; // 500MB stack.
    // lim.rlim_max = lim.rlim_cur; // Normal users may only be able to decrease this.

    // WARNING: Haven't yet figured out why this doesn't work on MacOS...
#ifndef __APPLE__
    code = setrlimit(RLIMIT_STACK, &lim);
    while (code) {
      fprintf(stderr, " [gibbon rts] Failed to set stack size to %llu, code %d\n", (unsigned long long)lim.rlim_cur, code);
      lim.rlim_cur /= 2;
      // lim.rlim_max /= 2;
      if(lim.rlim_cur < 100 * 1024) {
        fprintf(stderr, " [gibbon rts] Failed setrlimit stack size to something reasonable; giving up.\n");
        break; // abort();
      }
      int code = setrlimit(RLIMIT_STACK, &lim);
    }
#endif

    int got_numargs = 0; // How many numeric arguments have we got.

    int i;
    for (i = 1; i < argc; ++i)
    {
        if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
          show_usage(argv);
          exit(0);
        }
        else if (strcmp(argv[i], "--biginf-buffer-size") == 0 && i < argc - 1)
        {
            global_init_biginf_buf_size = atoll(argv[i + 1]);
            i++;
        }
        else if (strcmp(argv[i], "--inf-buffer-size") == 0 && i < argc - 1)
        {
            global_init_inf_buf_size = atoll(argv[i + 1]);
            i++;
        }
        else if ((strcmp(argv[i], "--bench-input") == 0)) {
          if (i+1 >= argc) {
            fprintf(stderr, "Not enough arguments after --bench-input, expected <file>.\n");
            show_usage(argv);
            exit(1);
          }
          global_benchfile_param = argv[i+1];
          i++;
        }
        else if ((strcmp(argv[i], "--array-input") == 0)) {
          if (i+1 >= argc) {
            fprintf(stderr, "Not enough arguments after --array-input, expected <file>.\n");
            show_usage(argv);
            exit(1);
          }
          global_arrayfile_param = argv[i+1];
          i++;
        }
        else if (strcmp(argv[i], "--array-input-length") == 0 && i < argc - 1) {
            global_arrayfile_length_param = atoll(argv[i+1]);
            i++;
        }
        else if (strcmp(argv[i], "--bench-prog") == 0 && i < argc - 1) {
            int len = strlen(argv[i+1]);
            global_bench_prog_param = (char*) malloc((len+1)*sizeof(char));
            strncpy(global_bench_prog_param,argv[i+1],len);
            i++;
        }
        // If present, we expect the two arguments to be <size> <iters>
        else if (got_numargs >= 2) {
            fprintf(stderr, "Extra arguments left over: ");
            for(; i < argc; i++) fprintf(stderr, "%s ", argv[i]);
            show_usage(argv);
            exit(1);
        } else {
          if (got_numargs == 0) {
            global_size_param  = atoll(argv[i]);
            got_numargs ++;
          } else {
            global_iters_param = atoll(argv[i]);
          }
        }
    }

    // Initialize global_bench_prog_param to an empty string in case
    // the runtime argument --bench-prog isn't passed.
    if (global_bench_prog_param == NULL) {
        global_bench_prog_param = (char*) malloc(1*sizeof(char));
        *global_bench_prog_param = '\n';
    }

    __main_expr();

    return 0;
}

// -----------------------------------------------------------------------------
// Program starts here
// -----------------------------------------------------------------------------

typedef struct Prod_struct { } Prod;
typedef struct Int64Prod_struct {
            IntTy field0;
        } Int64Prod;
typedef struct BoolProd_struct {
            BoolTy field0;
        } BoolProd;
typedef struct VectorProd_struct {
            VectorTy *field0;
        } VectorProd;
unsigned char bench_main();
unsigned char print_check(BoolTy b_418_2149_2744);
IntTy compare_int_original(IntTy r1_426_2152_2747, IntTy r2_427_2153_2748);
int compare_int(const void *r1_426_2152_2747, const void *r2_427_2153_2748);
IntTy maxInt(IntTy a_434_2154_2751, IntTy b_435_2155_2752);
IntTy minInt(IntTy a_444_2164_2754, IntTy b_445_2165_2755);
IntTy defaultGrainSize(IntTy n_633_2166_2757);
VectorTy *write_loop_1255(IntTy to_idx_345_2169_2762,
                          IntTy from_idx_346_2170_2763, IntTy end_347_2171_2764,
                          VectorTy *from_348_2172_2765,
                          VectorTy *to_349_2173_2766);
VectorTy *write_loop_seq_1249(IntTy to_idx_355_2188_2776,
                              IntTy from_idx_356_2189_2777,
                              IntTy end_357_2190_2778,
                              VectorTy *from_358_2191_2779,
                              VectorTy *to_359_2192_2780);
VectorTy *generate_par_loop_1242_1962(IntTy cutoff_745_2230_2807,
                                      VectorTy *vec_746_2231_2808,
                                      IntTy start_747_2232_2809,
                                      IntTy end_748_2233_2810,
                                      VectorTy *vec_412_2234_2811);
VectorTy *generate_loop_1241_1963(VectorTy *vec_579_2239_2819,
                                  IntTy idx_580_2240_2820,
                                  IntTy end_581_2241_2821,
                                  VectorTy *vec_412_2242_2822);
VectorTy *generate_loop_1241_1964(VectorTy *vec_579_2248_2829,
                                  IntTy idx_580_2249_2830,
                                  IntTy end_581_2250_2831);
VectorTy *generate_loop_1241_1965(VectorTy *vec_579_2256_2837,
                                  IntTy idx_580_2257_2838,
                                  IntTy end_581_2258_2839);
VectorTy *generate_loop_1241_1967(VectorTy *vec_579_2265_2845,
                                  IntTy idx_580_2266_2846,
                                  IntTy end_581_2267_2847,
                                  VectorTy *vec_415_2268_2848);
VectorTy *writeSort1_1252_1971(VectorTy *src_285_2292_2860,
                               VectorTy *tmp_286_2293_2861);
VectorTy *writeMerge_1254_1974(VectorTy *src_1_301_2306_2895,
                               VectorTy *src_2_302_2307_2896,
                               VectorTy *tmp_303_2308_2897);
IntTy binarySearch__1257_1977(IntTy lo_366_2327_2957, IntTy hi_367_2328_2958,
                              VectorTy *vec_369_2329_2959,
                              IntTy query_370_2330_2960);
VectorTy *writeSort2_1253_1973(VectorTy *src_253_2335_2976,
                               VectorTy *tmp_254_2336_2977);
VectorTy *writeMerge_seq_loop_1250_1978(IntTy i1_329_2357_3012,
                                        IntTy i2_330_2358_3013,
                                        IntTy j_331_2359_3014,
                                        IntTy n1_332_2360_3015,
                                        IntTy n2_333_2361_3016,
                                        VectorTy *src_1_335_2362_3017,
                                        VectorTy *src_2_336_2363_3018,
                                        VectorTy *tmp_337_2364_3019);
VectorTy *writeSort1_seq_1244_1980(VectorTy *src_270_2377_3053,
                                   VectorTy *tmp_271_2378_3054);
VectorTy *writeSort2_seq_1247_1981(VectorTy *src_237_2390_3093,
                                   VectorTy *tmp_238_2391_3094);
unsigned char check_sorted_1227_1948(VectorTy *sorted_207_2412_3134);
BoolTy ifoldl_loop_1240_1984(IntTy idx_503_2416_3148, IntTy end_504_2417_3149,
                             BoolTy acc_506_2418_3150,
                             VectorTy *vec_507_2419_3151,
                             VectorTy *arr1_210_2420_3152);
unsigned char bench_main()
{
    BoolTy fltIf_2632_2723 = strcmp("seqmergesort", global_bench_prog_param) ==
           0;

    if (fltIf_2632_2723) {
        IntTy n_190_2135_2724 = global_size_param;
        IntTy n__431_2245_2423_2726 =  maxInt(n_190_2135_2724, 0);
        IntTy tmp_7 = sizeof(IntTy);
        VectorTy *vec_432_2246_2424_2727 = vector_alloc(n__431_2245_2423_2726,
                                                        tmp_7);
        VectorTy *vec1_433_2247_2425_2728 =
                  generate_loop_1241_1964(vec_432_2246_2424_2727, 0, n__431_2245_2423_2726);
        VectorTy *timed_3247;
        VectorTy *times_5 = vector_alloc(global_iters_param, sizeof(double));
        struct timespec begin_timed_3247;
        struct timespec end_timed_3247;

        for (long long iters_timed_3247 = 0; iters_timed_3247 <
             global_iters_param; iters_timed_3247++) {
            if (iters_timed_3247 != global_iters_param - 1)
                save_alloc_state();
            clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_3247);

            IntTy n_428_2217_2451_2791_3165 =
                  vector_length(vec1_433_2247_2425_2728);
            IntTy n__431_2219_2453_2793_3167 =
                   maxInt(n_428_2217_2451_2791_3165, 0);
            IntTy tmp_1 = sizeof(IntTy);
            VectorTy *vec_432_2220_2454_2794_3168 =
                     vector_alloc(n__431_2219_2453_2793_3167, tmp_1);
            VectorTy *vec1_433_2221_2455_2795_3169 =
                      generate_loop_1241_1967(vec_432_2220_2454_2794_3168, 0, n__431_2219_2453_2793_3167, vec1_433_2247_2425_2728);
            IntTy vec_410_2178_2575_3050_3172 =
                  vector_length(vec1_433_2221_2455_2795_3169);
            IntTy tmp_0 = sizeof(IntTy);
            VectorTy *tmp_229_2375_3051_3173 =
                     vector_alloc(vec_410_2178_2575_3050_3172, tmp_0);
            VectorTy *tmp2_230_2376_3052_3174 =
                      writeSort1_seq_1244_1980(vec1_433_2221_2455_2795_3169, tmp_229_2375_3051_3173);

            timed_3247 = vec1_433_2221_2455_2795_3169;
            clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_3247);
            if (iters_timed_3247 != global_iters_param - 1)
                restore_alloc_state();

            double itertime_2 = difftimespecs(&begin_timed_3247,
                                              &end_timed_3247);

            vector_inplace_update(times_5, iters_timed_3247, &itertime_2);
        }
        vector_inplace_sort(times_5, compare_doubles);

        double *tmp_6 = (double *) vector_nth(times_5, global_iters_param / 2);
        double selftimed_4 = *tmp_6;
        double batchtime_3 = sum_timing_array(times_5);

        print_timing_array(times_5);
        printf("ITERS: %lld\n", global_iters_param);
        printf("SIZE: %lld\n", global_size_param);
        printf("BATCHTIME: %e\n", batchtime_3);
        printf("SELFTIMED: %e\n", selftimed_4);

        unsigned char tailapp_3219 =  check_sorted_1227_1948(timed_3247);

        return tailapp_3219;
    } else {
        IntTy n_194_2138_2734 = global_size_param;
        IntTy n__431_2253_2430_2736 =  maxInt(n_194_2138_2734, 0);
        IntTy tmp_15 = sizeof(IntTy);
        VectorTy *vec_432_2254_2431_2737 = vector_alloc(n__431_2253_2430_2736,
                                                        tmp_15);
        VectorTy *vec1_433_2255_2432_2738 =
                  generate_loop_1241_1965(vec_432_2254_2431_2737, 0, n__431_2253_2430_2736);
        VectorTy *timed_3248;
        VectorTy *times_13 = vector_alloc(global_iters_param, sizeof(double));
        struct timespec begin_timed_3248;
        struct timespec end_timed_3248;

        for (long long iters_timed_3248 = 0; iters_timed_3248 <
             global_iters_param; iters_timed_3248++) {
            if (iters_timed_3248 != global_iters_param - 1)
                save_alloc_state();
            clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_3248);

            IntTy n_738_2224_2457_2798_3177 =
                  vector_length(vec1_433_2255_2432_2738);
            IntTy n__741_2226_2459_2800_3179 =
                   maxInt(n_738_2224_2457_2798_3177, 0);
            IntTy tmp_9 = sizeof(IntTy);
            VectorTy *vec_742_2227_2460_2801_3180 =
                     vector_alloc(n__741_2226_2459_2800_3179, tmp_9);
            IntTy cutoff_743_2228_2461_2802_3181 =
                   defaultGrainSize(n__741_2226_2459_2800_3179);
            VectorTy *vec1_744_2229_2462_2803_3182 =
                      generate_par_loop_1242_1962(cutoff_743_2228_2461_2802_3181, vec_742_2227_2460_2801_3180, 0, n__741_2226_2459_2800_3179, vec1_433_2255_2432_2738);
            IntTy vec_410_2178_2487_2857_3185 =
                  vector_length(vec1_744_2229_2462_2803_3182);
            IntTy tmp_8 = sizeof(IntTy);
            VectorTy *tmp_234_2290_2858_3186 =
                     vector_alloc(vec_410_2178_2487_2857_3185, tmp_8);
            VectorTy *tmp2_235_2291_2859_3187 =
                      writeSort1_1252_1971(vec1_744_2229_2462_2803_3182, tmp_234_2290_2858_3186);

            timed_3248 = vec1_744_2229_2462_2803_3182;
            clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_3248);
            if (iters_timed_3248 != global_iters_param - 1)
                restore_alloc_state();

            double itertime_10 = difftimespecs(&begin_timed_3248,
                                               &end_timed_3248);

            vector_inplace_update(times_13, iters_timed_3248, &itertime_10);
        }
        vector_inplace_sort(times_13, compare_doubles);

        double *tmp_14 = (double *) vector_nth(times_13, global_iters_param /
                                               2);
        double selftimed_12 = *tmp_14;
        double batchtime_11 = sum_timing_array(times_13);

        print_timing_array(times_13);
        printf("ITERS: %lld\n", global_iters_param);
        printf("SIZE: %lld\n", global_size_param);
        printf("BATCHTIME: %e\n", batchtime_11);
        printf("SELFTIMED: %e\n", selftimed_12);

        unsigned char tailapp_3220 =  check_sorted_1227_1948(timed_3248);

        return tailapp_3220;
    }
}
unsigned char print_check(BoolTy b_418_2149_2744)
{
    if (b_418_2149_2744) {
        printf("OK\n");
        return 0;
    } else {
        printf("ERR\n");
        return 0;
    }
}
IntTy compare_int_original(IntTy r1_426_2152_2747, IntTy r2_427_2153_2748)
{
    BoolTy fltIf_2633_2749 = r1_426_2152_2747 < r2_427_2153_2748;

    if (fltIf_2633_2749) {
        IntTy tailprim_3225 = 0 - 1;

        return tailprim_3225;
    } else {
        BoolTy fltIf_2634_2750 = r1_426_2152_2747 > r2_427_2153_2748;

        if (fltIf_2634_2750) {
            return 1;
        } else {
            return 0;
        }
    }
}
int compare_int(const void *r1_426_2152_2747, const void *r2_427_2153_2748)
{
    IntTy fst_16 = *(IntTy *) r1_426_2152_2747;
    IntTy snd_17 = *(IntTy *) r2_427_2153_2748;

    return compare_int_original(fst_16, snd_17);
}
IntTy maxInt(IntTy a_434_2154_2751, IntTy b_435_2155_2752)
{
    BoolTy fltIf_2635_2753 = a_434_2154_2751 > b_435_2155_2752;

    if (fltIf_2635_2753) {
        return a_434_2154_2751;
    } else {
        return b_435_2155_2752;
    }
}
IntTy minInt(IntTy a_444_2164_2754, IntTy b_445_2165_2755)
{
    BoolTy fltIf_2636_2756 = a_444_2164_2754 < b_445_2165_2755;

    if (fltIf_2636_2756) {
        return a_444_2164_2754;
    } else {
        return b_445_2165_2755;
    }
}
IntTy defaultGrainSize(IntTy n_633_2166_2757)
{
    IntTy p_634_2167_2758 = get_num_processors();
    IntTy fltPrm_2638_2759 = 8 * p_634_2167_2758;
    IntTy fltAppE_2637_2760 = n_633_2166_2757 / fltPrm_2638_2759;
    IntTy grain_635_2168_2761 =  maxInt(1, fltAppE_2637_2760);
    IntTy tailapp_3226 =  minInt(2048, grain_635_2168_2761);

    return tailapp_3226;
}
VectorTy *write_loop_1255(IntTy to_idx_345_2169_2762,
                          IntTy from_idx_346_2170_2763, IntTy end_347_2171_2764,
                          VectorTy *from_348_2172_2765,
                          VectorTy *to_349_2173_2766)
{
    IntTy fltPrm_2640_2767 = end_347_2171_2764 - from_idx_346_2170_2763;
    BoolTy fltIf_2639_2768 = fltPrm_2640_2767 < 4096;

    if (fltIf_2639_2768) {
        VectorTy *tailapp_3227 =
                  write_loop_seq_1249(to_idx_345_2169_2762, from_idx_346_2170_2763, end_347_2171_2764, from_348_2172_2765, to_349_2173_2766);

        return tailapp_3227;
    } else {
        IntTy fltPrm_2641_2769 = from_idx_346_2170_2763 + end_347_2171_2764;
        IntTy mid_351_2174_2770 = fltPrm_2641_2769 / 2;
        IntTy parent_id_3214 = __cilkrts_get_worker_number();
        VectorTy *to1_352_2175_2771 =
                 cilk_spawn write_loop_1255(to_idx_345_2169_2762, from_idx_346_2170_2763, mid_351_2174_2770, from_348_2172_2765, to_349_2173_2766);
        IntTy fltPrm_2643_2772 = to_idx_345_2169_2762 + mid_351_2174_2770;
        IntTy fltAppE_2642_2773 = fltPrm_2643_2772 - from_idx_346_2170_2763;
        VectorTy *to2_353_2176_2774 =
                  write_loop_1255(fltAppE_2642_2773, mid_351_2174_2770, end_347_2171_2764, from_348_2172_2765, to_349_2173_2766);

        cilk_sync;
        return to2_353_2176_2774;
    }
}
VectorTy *write_loop_seq_1249(IntTy to_idx_355_2188_2776,
                              IntTy from_idx_356_2189_2777,
                              IntTy end_357_2190_2778,
                              VectorTy *from_358_2191_2779,
                              VectorTy *to_359_2192_2780)
{
    BoolTy fltIf_2644_2781 = from_idx_356_2189_2777 == end_357_2190_2778;

    if (fltIf_2644_2781) {
        return to_359_2192_2780;
    } else {
        IntTy *tmp_18;

        tmp_18 = (IntTy *) vector_nth(from_358_2191_2779,
                                      from_idx_356_2189_2777);

        IntTy val_393_2186_2449_2785 = *tmp_18;
        VectorTy *to1_361_2193_2787 = vector_inplace_update(to_359_2192_2780,
                                                            to_idx_355_2188_2776,
                                                            &val_393_2186_2449_2785);
        IntTy fltAppE_2645_2788 = to_idx_355_2188_2776 + 1;
        IntTy fltAppE_2646_2789 = from_idx_356_2189_2777 + 1;
        VectorTy *tailapp_3228 =
                  write_loop_seq_1249(fltAppE_2645_2788, fltAppE_2646_2789, end_357_2190_2778, from_358_2191_2779, to1_361_2193_2787);

        return tailapp_3228;
    }
}
VectorTy *generate_par_loop_1242_1962(IntTy cutoff_745_2230_2807,
                                      VectorTy *vec_746_2231_2808,
                                      IntTy start_747_2232_2809,
                                      IntTy end_748_2233_2810,
                                      VectorTy *vec_412_2234_2811)
{
    IntTy fltPrm_2648_2812 = end_748_2233_2810 - start_747_2232_2809;
    BoolTy fltIf_2647_2813 = fltPrm_2648_2812 <= cutoff_745_2230_2807;

    if (fltIf_2647_2813) {
        VectorTy *tailapp_3229 =
                  generate_loop_1241_1963(vec_746_2231_2808, start_747_2232_2809, end_748_2233_2810, vec_412_2234_2811);

        return tailapp_3229;
    } else {
        IntTy fltPrm_2649_2814 = start_747_2232_2809 + end_748_2233_2810;
        IntTy mid_751_2235_2815 = fltPrm_2649_2814 / 2;
        IntTy parent_id_3215 = __cilkrts_get_worker_number();
        VectorTy *_vec1_752_2236_2816 =
                 cilk_spawn generate_par_loop_1242_1962(cutoff_745_2230_2807, vec_746_2231_2808, start_747_2232_2809, mid_751_2235_2815, vec_412_2234_2811);
        VectorTy *vec2_753_2237_2817 =
                  generate_par_loop_1242_1962(cutoff_745_2230_2807, vec_746_2231_2808, mid_751_2235_2815, end_748_2233_2810, vec_412_2234_2811);

        cilk_sync;
        return vec2_753_2237_2817;
    }
}
VectorTy *generate_loop_1241_1963(VectorTy *vec_579_2239_2819,
                                  IntTy idx_580_2240_2820,
                                  IntTy end_581_2241_2821,
                                  VectorTy *vec_412_2242_2822)
{
    BoolTy fltIf_2650_2823 = idx_580_2240_2820 == end_581_2241_2821;

    if (fltIf_2650_2823) {
        return vec_579_2239_2819;
    } else {
        IntTy *tmp_19;

        tmp_19 = (IntTy *) vector_nth(vec_412_2242_2822, idx_580_2240_2820);

        IntTy fltPrm_2651_2826 = *tmp_19;
        VectorTy *vec1_584_2243_2827 = vector_inplace_update(vec_579_2239_2819,
                                                             idx_580_2240_2820,
                                                             &fltPrm_2651_2826);
        IntTy fltAppE_2652_2828 = idx_580_2240_2820 + 1;
        VectorTy *tailapp_3230 =
                  generate_loop_1241_1963(vec1_584_2243_2827, fltAppE_2652_2828, end_581_2241_2821, vec_412_2242_2822);

        return tailapp_3230;
    }
}
VectorTy *generate_loop_1241_1964(VectorTy *vec_579_2248_2829,
                                  IntTy idx_580_2249_2830,
                                  IntTy end_581_2250_2831)
{
    BoolTy fltIf_2653_2832 = idx_580_2249_2830 == end_581_2250_2831;

    if (fltIf_2653_2832) {
        return vec_579_2248_2829;
    } else {
        IntTy fltPrm_2654_2834 = rand();
        VectorTy *vec1_584_2251_2835 = vector_inplace_update(vec_579_2248_2829,
                                                             idx_580_2249_2830,
                                                             &fltPrm_2654_2834);
        IntTy fltAppE_2655_2836 = idx_580_2249_2830 + 1;
        VectorTy *tailapp_3231 =
                  generate_loop_1241_1964(vec1_584_2251_2835, fltAppE_2655_2836, end_581_2250_2831);

        return tailapp_3231;
    }
}
VectorTy *generate_loop_1241_1965(VectorTy *vec_579_2256_2837,
                                  IntTy idx_580_2257_2838,
                                  IntTy end_581_2258_2839)
{
    BoolTy fltIf_2656_2840 = idx_580_2257_2838 == end_581_2258_2839;

    if (fltIf_2656_2840) {
        return vec_579_2256_2837;
    } else {
        IntTy fltPrm_2657_2842 = rand();
        VectorTy *vec1_584_2259_2843 = vector_inplace_update(vec_579_2256_2837,
                                                             idx_580_2257_2838,
                                                             &fltPrm_2657_2842);
        IntTy fltAppE_2658_2844 = idx_580_2257_2838 + 1;
        VectorTy *tailapp_3232 =
                  generate_loop_1241_1965(vec1_584_2259_2843, fltAppE_2658_2844, end_581_2258_2839);

        return tailapp_3232;
    }
}
VectorTy *generate_loop_1241_1967(VectorTy *vec_579_2265_2845,
                                  IntTy idx_580_2266_2846,
                                  IntTy end_581_2267_2847,
                                  VectorTy *vec_415_2268_2848)
{
    BoolTy fltIf_2659_2849 = idx_580_2266_2846 == end_581_2267_2847;

    if (fltIf_2659_2849) {
        return vec_579_2265_2845;
    } else {
        IntTy *tmp_20;

        tmp_20 = (IntTy *) vector_nth(vec_415_2268_2848, idx_580_2266_2846);

        IntTy fltPrm_2660_2852 = *tmp_20;
        VectorTy *vec1_584_2269_2853 = vector_inplace_update(vec_579_2265_2845,
                                                             idx_580_2266_2846,
                                                             &fltPrm_2660_2852);
        IntTy fltAppE_2661_2854 = idx_580_2266_2846 + 1;
        VectorTy *tailapp_3233 =
                  generate_loop_1241_1967(vec1_584_2269_2853, fltAppE_2661_2854, end_581_2267_2847, vec_415_2268_2848);

        return tailapp_3233;
    }
}
VectorTy *writeSort1_1252_1971(VectorTy *src_285_2292_2860,
                               VectorTy *tmp_286_2293_2861)
{
    IntTy len_288_2294_2863 = vector_length(src_285_2292_2860);
    BoolTy fltIf_2662_2864 = len_288_2294_2863 < 8192;

    if (fltIf_2662_2864) {
        VectorTy *tailprim_3234 = vector_inplace_sort(src_285_2292_2860,
                                                      compare_int);

        return tailprim_3234;
    } else {
        IntTy half_289_2295_2866 = len_288_2294_2863 / 2;
        IntTy len_406_2181_2492_2869 = vector_length(src_285_2292_2860);
        IntTy n__407_2182_2493_2870 =  maxInt(half_289_2295_2866, 0);
        IntTy m_408_2183_2494_2871 =
               minInt(n__407_2182_2493_2870, len_406_2181_2492_2869);
        IntTy fltAppE_2663_2872 = len_406_2181_2492_2869 -
              n__407_2182_2493_2870;
        IntTy m__409_2184_2495_2873 =  maxInt(0, fltAppE_2663_2872);
        VectorTy *fltPrd_2664_2874 = vector_slice(0, m_408_2183_2494_2871,
                                                  src_285_2292_2860);
        VectorTy *fltPrd_2665_2875 = vector_slice(m_408_2183_2494_2871,
                                                  m__409_2184_2495_2873,
                                                  src_285_2292_2860);
        IntTy len_406_2181_2498_2881 = vector_length(tmp_286_2293_2861);
        IntTy n__407_2182_2499_2882 =  maxInt(half_289_2295_2866, 0);
        IntTy m_408_2183_2500_2883 =
               minInt(n__407_2182_2499_2882, len_406_2181_2498_2881);
        IntTy fltAppE_2666_2884 = len_406_2181_2498_2881 -
              n__407_2182_2499_2882;
        IntTy m__409_2184_2501_2885 =  maxInt(0, fltAppE_2666_2884);
        VectorTy *fltPrd_2667_2886 = vector_slice(0, m_408_2183_2500_2883,
                                                  tmp_286_2293_2861);
        VectorTy *fltPrd_2668_2887 = vector_slice(m_408_2183_2500_2883,
                                                  m__409_2184_2501_2885,
                                                  tmp_286_2293_2861);
        IntTy parent_id_3216 = __cilkrts_get_worker_number();
        VectorTy *tmp_l1_296_2302_2891 =
                 cilk_spawn writeSort2_1253_1973(fltPrd_2664_2874, fltPrd_2667_2886);
        VectorTy *tmp_r1_297_2303_2892 =
                  writeSort2_1253_1973(fltPrd_2665_2875, fltPrd_2668_2887);

        cilk_sync;

        VectorTy *res_299_2305_2894 =
                  writeMerge_1254_1974(tmp_l1_296_2302_2891, tmp_r1_297_2303_2892, src_285_2292_2860);

        return res_299_2305_2894;
    }
}
VectorTy *writeMerge_1254_1974(VectorTy *src_1_301_2306_2895,
                               VectorTy *src_2_302_2307_2896,
                               VectorTy *tmp_303_2308_2897)
{
    IntTy fltPrm_2670_2899 = vector_length(tmp_303_2308_2897);
    BoolTy fltIf_2669_2900 = fltPrm_2670_2899 < 4096;

    if (fltIf_2669_2900) {
        IntTy n1_326_2354_2506_2904 = vector_length(src_1_301_2306_2895);
        IntTy n2_327_2355_2507_2905 = vector_length(src_2_302_2307_2896);
        VectorTy *res_328_2356_2508_2906 =
                  writeMerge_seq_loop_1250_1978(0, 0, 0, n1_326_2354_2506_2904, n2_327_2355_2507_2905, src_1_301_2306_2895, src_2_302_2307_2896, tmp_303_2308_2897);

        return res_328_2356_2508_2906;
    } else {
        IntTy n1_305_2309_2908 = vector_length(src_1_301_2306_2895);
        IntTy n2_306_2310_2910 = vector_length(src_2_302_2307_2896);
        BoolTy fltIf_2671_2911 = n1_305_2309_2908 == 0;

        if (fltIf_2671_2911) {
            VectorTy *tailapp_3235 =
                      write_loop_1255(0, 0, n2_306_2310_2910, src_2_302_2307_2896, tmp_303_2308_2897);

            return tailapp_3235;
        } else {
            IntTy mid1_307_2311_2912 = n1_305_2309_2908 / 2;
            IntTy *tmp_21;

            tmp_21 = (IntTy *) vector_nth(src_1_301_2306_2895,
                                          mid1_307_2311_2912);

            IntTy pivot_308_2312_2915 = *tmp_21;
            IntTy fltAppE_2672_2918 = vector_length(src_2_302_2307_2896);
            IntTy mid2_309_2313_2919 =
                   binarySearch__1257_1977(0, fltAppE_2672_2918, src_2_302_2307_2896, pivot_308_2312_2915);
            VectorTy *src_1_l_310_2314_2923 = vector_slice(0,
                                                           mid1_307_2311_2912,
                                                           src_1_301_2306_2895);
            IntTy i_396_2196_2518_2924 = mid1_307_2311_2912 + 1;
            IntTy fltPrm_2673_2925 = mid1_307_2311_2912 + 1;
            IntTy n_397_2197_2519_2926 = n1_305_2309_2908 - fltPrm_2673_2925;
            VectorTy *src_1_r_311_2315_2928 = vector_slice(i_396_2196_2518_2924,
                                                           n_397_2197_2519_2926,
                                                           src_1_301_2306_2895);
            VectorTy *src_2_l_312_2316_2932 = vector_slice(0,
                                                           mid2_309_2313_2919,
                                                           src_2_302_2307_2896);
            IntTy n_397_2197_2525_2934 = n2_306_2310_2910 - mid2_309_2313_2919;
            VectorTy *src_2_r_313_2317_2936 = vector_slice(mid2_309_2313_2919,
                                                           n_397_2197_2525_2934,
                                                           src_2_302_2307_2896);
            IntTy i_392_2185_2527_2937 = mid1_307_2311_2912 +
                  mid2_309_2313_2919;
            VectorTy *wildcard__67_314_2318_2940 =
                     vector_inplace_update(tmp_303_2308_2897,
                                           i_392_2185_2527_2937,
                                           &pivot_308_2312_2915);
            IntTy len_t_315_2319_2942 = vector_length(tmp_303_2308_2897);
            IntTy n_397_2197_2532_2944 = mid1_307_2311_2912 +
                  mid2_309_2313_2919;
            VectorTy *tmp_l_316_2320_2946 = vector_slice(0,
                                                         n_397_2197_2532_2944,
                                                         tmp_303_2308_2897);
            IntTy fltPrm_2674_2947 = mid1_307_2311_2912 + mid2_309_2313_2919;
            IntTy i_396_2196_2534_2948 = fltPrm_2674_2947 + 1;
            IntTy fltPrm_2676_2949 = mid1_307_2311_2912 + mid2_309_2313_2919;
            IntTy fltPrm_2675_2950 = fltPrm_2676_2949 + 1;
            IntTy n_397_2197_2535_2951 = len_t_315_2319_2942 - fltPrm_2675_2950;
            VectorTy *tmp_r_317_2321_2953 = vector_slice(i_396_2196_2534_2948,
                                                         n_397_2197_2535_2951,
                                                         tmp_303_2308_2897);
            IntTy parent_id_3217 = __cilkrts_get_worker_number();
            VectorTy *tmp_l1_318_2322_2954 =
                     cilk_spawn writeMerge_1254_1974(src_1_l_310_2314_2923, src_2_l_312_2316_2932, tmp_l_316_2320_2946);
            VectorTy *tmp_r1_319_2323_2955 =
                      writeMerge_1254_1974(src_1_r_311_2315_2928, src_2_r_313_2317_2936, tmp_r_317_2321_2953);

            cilk_sync;
            return tmp_303_2308_2897;
        }
    }
}
IntTy binarySearch__1257_1977(IntTy lo_366_2327_2957, IntTy hi_367_2328_2958,
                              VectorTy *vec_369_2329_2959,
                              IntTy query_370_2330_2960)
{
    IntTy n_372_2331_2961 = hi_367_2328_2958 - lo_366_2327_2957;
    BoolTy fltIf_2677_2962 = n_372_2331_2961 == 0;

    if (fltIf_2677_2962) {
        return lo_366_2327_2957;
    } else {
        IntTy fltPrm_2678_2963 = n_372_2331_2961 / 2;
        IntTy mid_373_2332_2964 = lo_366_2327_2957 + fltPrm_2678_2963;
        IntTy *tmp_22;

        tmp_22 = (IntTy *) vector_nth(vec_369_2329_2959, mid_373_2332_2964);

        IntTy pivot_374_2333_2967 = *tmp_22;
        BoolTy fltIf_2679_2970 = query_370_2330_2960 < pivot_374_2333_2967;
        IntTy tst_375_2334_2972;

        if (fltIf_2679_2970) {
            IntTy flt_3255 = 0 - 1;

            tst_375_2334_2972 = flt_3255;
        } else {
            BoolTy fltIf_2680_2971 = query_370_2330_2960 > pivot_374_2333_2967;

            if (fltIf_2680_2971) {
                tst_375_2334_2972 = 1;
            } else {
                tst_375_2334_2972 = 0;
            }
        }

        BoolTy fltIf_2681_2973 = tst_375_2334_2972 < 0;

        if (fltIf_2681_2973) {
            IntTy tailapp_3236 =
                   binarySearch__1257_1977(lo_366_2327_2957, mid_373_2332_2964, vec_369_2329_2959, query_370_2330_2960);

            return tailapp_3236;
        } else {
            BoolTy fltIf_2682_2974 = tst_375_2334_2972 > 0;

            if (fltIf_2682_2974) {
                IntTy fltAppE_2683_2975 = mid_373_2332_2964 + 1;
                IntTy tailapp_3237 =
                       binarySearch__1257_1977(fltAppE_2683_2975, hi_367_2328_2958, vec_369_2329_2959, query_370_2330_2960);

                return tailapp_3237;
            } else {
                return mid_373_2332_2964;
            }
        }
    }
}
VectorTy *writeSort2_1253_1973(VectorTy *src_253_2335_2976,
                               VectorTy *tmp_254_2336_2977)
{
    IntTy len_256_2337_2979 = vector_length(src_253_2335_2976);
    BoolTy fltIf_2684_2980 = len_256_2337_2979 < 8192;

    if (fltIf_2684_2980) {
        VectorTy *tmp_1_257_2338_2981 =
                  write_loop_1255(0, 0, len_256_2337_2979, src_253_2335_2976, tmp_254_2336_2977);
        VectorTy *tailprim_3238 = vector_inplace_sort(tmp_1_257_2338_2981,
                                                      compare_int);

        return tailprim_3238;
    } else {
        IntTy half_258_2339_2983 = len_256_2337_2979 / 2;
        IntTy len_406_2181_2546_2986 = vector_length(src_253_2335_2976);
        IntTy n__407_2182_2547_2987 =  maxInt(half_258_2339_2983, 0);
        IntTy m_408_2183_2548_2988 =
               minInt(n__407_2182_2547_2987, len_406_2181_2546_2986);
        IntTy fltAppE_2685_2989 = len_406_2181_2546_2986 -
              n__407_2182_2547_2987;
        IntTy m__409_2184_2549_2990 =  maxInt(0, fltAppE_2685_2989);
        VectorTy *fltPrd_2686_2991 = vector_slice(0, m_408_2183_2548_2988,
                                                  src_253_2335_2976);
        VectorTy *fltPrd_2687_2992 = vector_slice(m_408_2183_2548_2988,
                                                  m__409_2184_2549_2990,
                                                  src_253_2335_2976);
        IntTy len_406_2181_2552_2998 = vector_length(tmp_254_2336_2977);
        IntTy n__407_2182_2553_2999 =  maxInt(half_258_2339_2983, 0);
        IntTy m_408_2183_2554_3000 =
               minInt(n__407_2182_2553_2999, len_406_2181_2552_2998);
        IntTy fltAppE_2688_3001 = len_406_2181_2552_2998 -
              n__407_2182_2553_2999;
        IntTy m__409_2184_2555_3002 =  maxInt(0, fltAppE_2688_3001);
        VectorTy *fltPrd_2689_3003 = vector_slice(0, m_408_2183_2554_3000,
                                                  tmp_254_2336_2977);
        VectorTy *fltPrd_2690_3004 = vector_slice(m_408_2183_2554_3000,
                                                  m__409_2184_2555_3002,
                                                  tmp_254_2336_2977);
        IntTy parent_id_3218 = __cilkrts_get_worker_number();
        VectorTy *src_l1_265_2346_3008 =
                 cilk_spawn writeSort1_1252_1971(fltPrd_2686_2991, fltPrd_2689_3003);
        VectorTy *src_r1_266_2347_3009 =
                  writeSort1_1252_1971(fltPrd_2687_2992, fltPrd_2690_3004);

        cilk_sync;

        VectorTy *res_268_2349_3011 =
                  writeMerge_1254_1974(src_l1_265_2346_3008, src_r1_266_2347_3009, tmp_254_2336_2977);

        return res_268_2349_3011;
    }
}
VectorTy *writeMerge_seq_loop_1250_1978(IntTy i1_329_2357_3012,
                                        IntTy i2_330_2358_3013,
                                        IntTy j_331_2359_3014,
                                        IntTy n1_332_2360_3015,
                                        IntTy n2_333_2361_3016,
                                        VectorTy *src_1_335_2362_3017,
                                        VectorTy *src_2_336_2363_3018,
                                        VectorTy *tmp_337_2364_3019)
{
    BoolTy fltIf_2691_3020 = i1_329_2357_3012 == n1_332_2360_3015;

    if (fltIf_2691_3020) {
        VectorTy *tmp_2_339_2365_3021 =
                  write_loop_seq_1249(j_331_2359_3014, i2_330_2358_3013, n2_333_2361_3016, src_2_336_2363_3018, tmp_337_2364_3019);

        return tmp_2_339_2365_3021;
    } else {
        BoolTy fltIf_2692_3022 = i2_330_2358_3013 == n2_333_2361_3016;

        if (fltIf_2692_3022) {
            VectorTy *tmp_2_340_2366_3023 =
                      write_loop_seq_1249(j_331_2359_3014, i1_329_2357_3012, n1_332_2360_3015, src_1_335_2362_3017, tmp_337_2364_3019);

            return tmp_2_340_2366_3023;
        } else {
            IntTy *tmp_24;

            tmp_24 = (IntTy *) vector_nth(src_1_335_2362_3017,
                                          i1_329_2357_3012);

            IntTy x1_341_2367_3026 = *tmp_24;
            IntTy *tmp_23;

            tmp_23 = (IntTy *) vector_nth(src_2_336_2363_3018,
                                          i2_330_2358_3013);

            IntTy x2_342_2368_3029 = *tmp_23;
            BoolTy fltIf_2695_3032 = x1_341_2367_3026 < x2_342_2368_3029;
            IntTy fltPrm_2694_3034;

            if (fltIf_2695_3032) {
                IntTy flt_3260 = 0 - 1;

                fltPrm_2694_3034 = flt_3260;
            } else {
                BoolTy fltIf_2696_3033 = x1_341_2367_3026 > x2_342_2368_3029;

                if (fltIf_2696_3033) {
                    fltPrm_2694_3034 = 1;
                } else {
                    fltPrm_2694_3034 = 0;
                }
            }

            BoolTy fltIf_2693_3035 = fltPrm_2694_3034 < 0;

            if (fltIf_2693_3035) {
                VectorTy *tmp_1_343_2369_3039 =
                         vector_inplace_update(tmp_337_2364_3019,
                                               j_331_2359_3014,
                                               &x1_341_2367_3026);
                IntTy fltAppE_2697_3040 = i1_329_2357_3012 + 1;
                IntTy fltAppE_2698_3041 = j_331_2359_3014 + 1;
                VectorTy *tailapp_3239 =
                          writeMerge_seq_loop_1250_1978(fltAppE_2697_3040, i2_330_2358_3013, fltAppE_2698_3041, n1_332_2360_3015, n2_333_2361_3016, src_1_335_2362_3017, src_2_336_2363_3018, tmp_1_343_2369_3039);

                return tailapp_3239;
            } else {
                VectorTy *tmp_1_344_2370_3045 =
                         vector_inplace_update(tmp_337_2364_3019,
                                               j_331_2359_3014,
                                               &x2_342_2368_3029);
                IntTy fltAppE_2699_3046 = i2_330_2358_3013 + 1;
                IntTy fltAppE_2700_3047 = j_331_2359_3014 + 1;
                VectorTy *tailapp_3240 =
                          writeMerge_seq_loop_1250_1978(i1_329_2357_3012, fltAppE_2699_3046, fltAppE_2700_3047, n1_332_2360_3015, n2_333_2361_3016, src_1_335_2362_3017, src_2_336_2363_3018, tmp_1_344_2370_3045);

                return tailapp_3240;
            }
        }
    }
}
VectorTy *writeSort1_seq_1244_1980(VectorTy *src_270_2377_3053,
                                   VectorTy *tmp_271_2378_3054)
{
    IntTy len_273_2379_3056 = vector_length(src_270_2377_3053);
    BoolTy fltIf_2701_3057 = len_273_2379_3056 < 8192;

    if (fltIf_2701_3057) {
        VectorTy *tailprim_3241 = vector_inplace_sort(src_270_2377_3053,
                                                      compare_int);

        return tailprim_3241;
    } else {
        IntTy half_274_2380_3059 = len_273_2379_3056 / 2;
        IntTy len_406_2181_2580_3062 = vector_length(src_270_2377_3053);
        IntTy n__407_2182_2581_3063 =  maxInt(half_274_2380_3059, 0);
        IntTy m_408_2183_2582_3064 =
               minInt(n__407_2182_2581_3063, len_406_2181_2580_3062);
        IntTy fltAppE_2702_3065 = len_406_2181_2580_3062 -
              n__407_2182_2581_3063;
        IntTy m__409_2184_2583_3066 =  maxInt(0, fltAppE_2702_3065);
        VectorTy *fltPrd_2703_3067 = vector_slice(0, m_408_2183_2582_3064,
                                                  src_270_2377_3053);
        VectorTy *fltPrd_2704_3068 = vector_slice(m_408_2183_2582_3064,
                                                  m__409_2184_2583_3066,
                                                  src_270_2377_3053);
        IntTy len_406_2181_2586_3074 = vector_length(tmp_271_2378_3054);
        IntTy n__407_2182_2587_3075 =  maxInt(half_274_2380_3059, 0);
        IntTy m_408_2183_2588_3076 =
               minInt(n__407_2182_2587_3075, len_406_2181_2586_3074);
        IntTy fltAppE_2705_3077 = len_406_2181_2586_3074 -
              n__407_2182_2587_3075;
        IntTy m__409_2184_2589_3078 =  maxInt(0, fltAppE_2705_3077);
        VectorTy *fltPrd_2706_3079 = vector_slice(0, m_408_2183_2588_3076,
                                                  tmp_271_2378_3054);
        VectorTy *fltPrd_2707_3080 = vector_slice(m_408_2183_2588_3076,
                                                  m__409_2184_2589_3078,
                                                  tmp_271_2378_3054);
        VectorTy *tmp_l1_281_2387_3084 =
                  writeSort2_seq_1247_1981(fltPrd_2703_3067, fltPrd_2706_3079);
        VectorTy *tmp_r1_282_2388_3085 =
                  writeSort2_seq_1247_1981(fltPrd_2704_3068, fltPrd_2707_3080);
        IntTy n1_326_2354_2593_3089 = vector_length(tmp_l1_281_2387_3084);
        IntTy n2_327_2355_2594_3090 = vector_length(tmp_r1_282_2388_3085);
        VectorTy *res_328_2356_2595_3091 =
                  writeMerge_seq_loop_1250_1978(0, 0, 0, n1_326_2354_2593_3089, n2_327_2355_2594_3090, tmp_l1_281_2387_3084, tmp_r1_282_2388_3085, src_270_2377_3053);

        return res_328_2356_2595_3091;
    }
}
VectorTy *writeSort2_seq_1247_1981(VectorTy *src_237_2390_3093,
                                   VectorTy *tmp_238_2391_3094)
{
    IntTy len_240_2392_3096 = vector_length(src_237_2390_3093);
    BoolTy fltIf_2708_3097 = len_240_2392_3096 < 8192;

    if (fltIf_2708_3097) {
        VectorTy *tmp_1_241_2393_3098 =
                  write_loop_seq_1249(0, 0, len_240_2392_3096, src_237_2390_3093, tmp_238_2391_3094);
        VectorTy *tailprim_3242 = vector_inplace_sort(tmp_1_241_2393_3098,
                                                      compare_int);

        return tailprim_3242;
    } else {
        IntTy half_242_2394_3100 = len_240_2392_3096 / 2;
        IntTy len_406_2181_2600_3103 = vector_length(src_237_2390_3093);
        IntTy n__407_2182_2601_3104 =  maxInt(half_242_2394_3100, 0);
        IntTy m_408_2183_2602_3105 =
               minInt(n__407_2182_2601_3104, len_406_2181_2600_3103);
        IntTy fltAppE_2709_3106 = len_406_2181_2600_3103 -
              n__407_2182_2601_3104;
        IntTy m__409_2184_2603_3107 =  maxInt(0, fltAppE_2709_3106);
        VectorTy *fltPrd_2710_3108 = vector_slice(0, m_408_2183_2602_3105,
                                                  src_237_2390_3093);
        VectorTy *fltPrd_2711_3109 = vector_slice(m_408_2183_2602_3105,
                                                  m__409_2184_2603_3107,
                                                  src_237_2390_3093);
        IntTy len_406_2181_2606_3115 = vector_length(tmp_238_2391_3094);
        IntTy n__407_2182_2607_3116 =  maxInt(half_242_2394_3100, 0);
        IntTy m_408_2183_2608_3117 =
               minInt(n__407_2182_2607_3116, len_406_2181_2606_3115);
        IntTy fltAppE_2712_3118 = len_406_2181_2606_3115 -
              n__407_2182_2607_3116;
        IntTy m__409_2184_2609_3119 =  maxInt(0, fltAppE_2712_3118);
        VectorTy *fltPrd_2713_3120 = vector_slice(0, m_408_2183_2608_3117,
                                                  tmp_238_2391_3094);
        VectorTy *fltPrd_2714_3121 = vector_slice(m_408_2183_2608_3117,
                                                  m__409_2184_2609_3119,
                                                  tmp_238_2391_3094);
        VectorTy *src_l1_249_2401_3125 =
                  writeSort1_seq_1244_1980(fltPrd_2710_3108, fltPrd_2713_3120);
        VectorTy *src_r1_250_2402_3126 =
                  writeSort1_seq_1244_1980(fltPrd_2711_3109, fltPrd_2714_3121);
        IntTy n1_326_2354_2613_3130 = vector_length(src_l1_249_2401_3125);
        IntTy n2_327_2355_2614_3131 = vector_length(src_r1_250_2402_3126);
        VectorTy *res_328_2356_2615_3132 =
                  writeMerge_seq_loop_1250_1978(0, 0, 0, n1_326_2354_2613_3130, n2_327_2355_2614_3131, src_l1_249_2401_3125, src_r1_250_2402_3126, tmp_238_2391_3094);

        return res_328_2356_2615_3132;
    }
}
unsigned char check_sorted_1227_1948(VectorTy *sorted_207_2412_3134)
{
    IntTy len_209_2413_3136 = vector_length(sorted_207_2412_3134);
    BoolTy fltIf_2715_3137 = len_209_2413_3136 <= 1;

    if (fltIf_2715_3137) {
        unsigned char tailapp_3243 =  print_check(true);

        return tailapp_3243;
    } else {
        IntTy n_397_2197_2622_3140 = len_209_2413_3136 - 2;
        VectorTy *arr1_210_2414_3142 = vector_slice(0, n_397_2197_2622_3140,
                                                    sorted_207_2412_3134);
        IntTy fltAppE_2717_3146 = vector_length(arr1_210_2414_3142);
        BoolTy check_215_2415_3147 =
                ifoldl_loop_1240_1984(0, fltAppE_2717_3146, true, arr1_210_2414_3142, arr1_210_2414_3142);
        unsigned char tailapp_3244 =  print_check(check_215_2415_3147);

        return tailapp_3244;
    }
}
BoolTy ifoldl_loop_1240_1984(IntTy idx_503_2416_3148, IntTy end_504_2417_3149,
                             BoolTy acc_506_2418_3150,
                             VectorTy *vec_507_2419_3151,
                             VectorTy *arr1_210_2420_3152)
{
    BoolTy fltIf_2718_3153 = idx_503_2416_3148 == end_504_2417_3149;

    if (fltIf_2718_3153) {
        return acc_506_2418_3150;
    } else {
        IntTy *tmp_26;

        tmp_26 = (IntTy *) vector_nth(vec_507_2419_3151, idx_503_2416_3148);

        IntTy elt1_211_2406_2629_3156 = *tmp_26;
        IntTy fltAppE_2719_3158 = idx_503_2416_3148 + 1;
        IntTy *tmp_25;

        tmp_25 = (IntTy *) vector_nth(arr1_210_2420_3152, fltAppE_2719_3158);

        IntTy elt2_214_2408_2631_3159 = *tmp_25;
        BoolTy fltIf_2633_2749_3208 = elt1_211_2406_2629_3156 <
               elt2_214_2408_2631_3159;
        IntTy fltPrm_2721_3160;

        if (fltIf_2633_2749_3208) {
            IntTy flt_3269 = 0 - 1;

            fltPrm_2721_3160 = flt_3269;
        } else {
            BoolTy fltIf_2634_2750_3209 = elt1_211_2406_2629_3156 >
                   elt2_214_2408_2631_3159;

            if (fltIf_2634_2750_3209) {
                fltPrm_2721_3160 = 1;
            } else {
                fltPrm_2721_3160 = 0;
            }
        }

        BoolTy fltPrm_2720_3161 = fltPrm_2721_3160 <= 0;
        BoolTy acc1_510_2421_3162 = acc_506_2418_3150 && fltPrm_2720_3161;
        IntTy fltAppE_2722_3163 = idx_503_2416_3148 + 1;
        BoolTy tailapp_3245 =
                ifoldl_loop_1240_1984(fltAppE_2722_3163, end_504_2417_3149, acc1_510_2421_3162, vec_507_2419_3151, arr1_210_2420_3152);

        return tailapp_3245;
    }
}
int __main_expr()
{
    //add_symbol(3249, "OK\n");
    //add_symbol(3250, "Err\n");

    unsigned char tailapp_3246 =  bench_main();

    printf("'#()");
    printf("\n");
    return 0;
}
