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
#include <utlist.h>
#include <uthash.h>
#include <utarray.h>
#ifdef _POINTER
#include <gc.h>
#endif
#ifdef _PARALLEL
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#endif

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
// Arenas and dictionaries
// -------------------------------------

typedef struct mem_arena {
  int ind;
  char* mem; // TODO(vollmerm): make this a list of chunks?
  void* reflist;
} mem_arena_t;

typedef mem_arena_t* ArenaTy;

ArenaTy alloc_arena() {
  ArenaTy ar = ALLOC(sizeof(mem_arena_t));
  ar->ind = 0;
  ar->mem = malloc(global_inf_buf_max_chunk_size);
  ar->reflist = 0;
  return ar;
}

void free_arena(ArenaTy ar) {
  free(ar->mem);
  // TODO(vollmerm): free everything in ar->reflist
  free(ar);
}

CursorTy extend_arena(ArenaTy ar, int size) {
  CursorTy ret = ar->mem + ar->ind;
  ar->ind += size;
  return ret;
}

typedef struct dict_item {
  struct dict_item * next;
  int key;
  void * ptrval;
} dict_item_t;

dict_item_t * dict_alloc(ArenaTy ar) {
  return (dict_item_t *) extend_arena(ar, sizeof(dict_item_t)); // ALLOC(sizeof(dict_item_t));
}

dict_item_t *dict_insert_ptr(ArenaTy ar, dict_item_t *ptr, SymTy key, PtrTy val) {
  dict_item_t *ret = dict_alloc(ar);
  ret->key = key;
  ret->ptrval = val;
  ret->next = ptr;
  return ret;
}

PtrTy dict_lookup_ptr(dict_item_t *ptr, SymTy key) {
  while (ptr != 0) {
    if (ptr->key == key) {
      return ptr->ptrval;
    } else {
      ptr = ptr->next;
    }
  }
  printf("Error, key %lld not found!\n",key);
  exit(1);
}

// -------------------------------------
// Sets
// -------------------------------------


struct set_elem {
  int val;
  UT_hash_handle hh;
};

typedef struct set_elem* SymSetTy;

SymSetTy empty_set() {
  return NULL;
}

SymSetTy insert_set(SymSetTy set, int sym) {
  SymSetTy s;
  HASH_FIND_INT(set, &sym, s);  /* sym already in the hash? */
  if (s==NULL) {
    s = malloc(sizeof(struct set_elem));
    s->val = sym;
    HASH_ADD_INT(set,val,s);
  }
  return set;
}

BoolTy contains_set(SymSetTy set, int sym) {
  SymSetTy s;
  HASH_FIND_INT(set, &sym, s);
  return (s!=NULL);
}

// -------------------------------------
// Sym Hash
// -------------------------------------

struct sym_hash_elem {
  int key;
  int val;
  UT_hash_handle hh;
};

typedef struct sym_hash_elem* SymHashTy;

typedef struct sym_hash_elem* IntHashTy;

SymHashTy empty_hash() {
  return NULL;
}

SymHashTy insert_hash(SymHashTy hash, int k, int v) {
  SymHashTy s;
  // NOTE: not checking for duplicates!
  // s = malloc(sizeof(struct sym_hash_elem));
  s = ALLOC(sizeof(struct sym_hash_elem));
  s->val = v;
  s->key = k;
  HASH_ADD_INT(hash,key,s);

  return hash;
}

IntTy lookup_hash(SymHashTy hash, int k) {
  SymHashTy s;
  HASH_FIND_INT(hash,&k,s);
  if (s==NULL) {
    return k; // NOTE: return original key if val not found
              // TODO(vollmerm): come up with something better to do here
  } else {
    return s->val;
  }
}

BoolTy contains_hash(SymHashTy hash, int sym) {
  SymHashTy s;
  HASH_FIND_INT(hash,&sym,s);
  return (s!=NULL);
}

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

static SymTy newline_symbol = -1;
static SymTy space_symbol = -1;
static SymTy comma_symbol = -1;
static SymTy leftparen_symbol = -1;
static SymTy rightparen_symbol = -1;

typedef struct SymTable_elem {
    SymTy idx;                 /* key */
    char value[global_max_symbol_len];
    UT_hash_handle hh;         /* makes this structure hashable */
} SymTable_elem;

// important! initialize to NULL
SymTable_elem *global_sym_table = NULL;

void add_symbol(SymTy idx, char *value) {
    struct SymTable_elem *s;
    s = ALLOC(sizeof(struct SymTable_elem));
    s->idx = idx;
    strcpy(s->value, value);
    HASH_ADD(hh, global_sym_table, idx, sizeof(IntTy), s);
    if (idx > global_gensym_counter) {
        global_gensym_counter = idx;
    }
}

void set_newline(SymTy idx) {
  newline_symbol = idx;
  add_symbol(idx,"NEWLINE");
}

void set_space(SymTy idx) {
  space_symbol = idx;
  add_symbol(idx,"SPACE");
}

void set_comma(SymTy idx) {
  comma_symbol = idx;
  add_symbol(idx,"COMMA");
}

void set_leftparen(SymTy idx) {
  leftparen_symbol = idx;
  add_symbol(idx,"LEFTPAREN");
}

void set_rightparen(SymTy idx) {
  rightparen_symbol = idx;
  add_symbol(idx,"RIGHTPAREN");
}

IntTy print_symbol(SymTy idx) {
  if (idx == comma_symbol) {
    return printf(",");
  } else if (idx == newline_symbol) {
    return printf("\n");
  } else if (idx == space_symbol) {
    return printf(" ");
  } else if (idx == leftparen_symbol) {
    return printf("(");
  } else if (idx == rightparen_symbol) {
    return printf(")");
  } else {
    struct SymTable_elem *s;
    HASH_FIND(hh, global_sym_table, &idx, sizeof(SymTy), s);
    if (s == NULL) {
        return printf("%lld", idx);
    } else {
        return printf("%s", s->value);
    }

  }
}

#ifdef _PARALLEL
SymTy gensym() {
    SymTy idx = __atomic_add_fetch(&global_gensym_counter, 1, __ATOMIC_SEQ_CST);
    return idx;
}
#else
SymTy gensym() {
    global_gensym_counter += 1;
    SymTy idx = global_gensym_counter;
    return idx;
}
#endif

void free_symtable() {
    struct SymTable_elem *elt, *tmp;
    HASH_ITER(hh, global_sym_table, elt, tmp) {
        HASH_DEL(global_sym_table,elt);
    }
    free(elt);
    free(tmp);
}

/*

----------------------------------------
Garbage collection
----------------------------------------

   Gibbon has "growing regions" i.e each logical region is backed by a doubly linked-list
   of smaller chunks which grows as required. In addition to actual data, each chunk
   stores some additional metadata (RegionFooter) to chain the chunks together in a list
   and for garbage collection. The footer:

   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   serialized data | rf_reg_metadata_ptr | rf_seq_no | rf_size | rf_next | rf_prev
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   The metadata after the serialized data serves various purposes:

   - rf_reg_metadata_ptr: A pointer to a RegionTy struct that contains various metadata.
     Of particular interest to us are the fields:

     = reg_id: A unique identifier for a region.

     = refcount and outset: Whenever an inter-region indirection is created, we record that information
       using these two fields. Suppose we have an indirection from region A that points to some chunk
       in region B. Then A's outset will store a pointer to that chunk's footer, and B's refcount will
       be bumped by 1. Note that all there's only 1 refcount cell, and 1 outset per logical region,
       and chunks only store a pointer to them.

   - rf_seq_no: The index of this particular chunk in the list.

   - rf_size: Used during bounds checking to calculate the size of the next region in
     the linked list.

   - rf_next / rf_prev: Point to the next and previous chunk respectively.


There are two ways in which a region may be freed:

(1) Whenever it goes out of scope

  The RTS tries to free a region whenever it goes out of scope. But this doesn't always succeed as
  regions sometimes contain values that "escape". One reason why this'll happen is if there's an
  indirection from A->B, and A lives longer than B.
  In such a case, when B goes out of scope it's refcount won't be 0, and the RTS won't free it.
  This brings us to (2).

(2)

  When the RTS successfully frees a region, it decrements the refcounts of all the regions it
  points to (via the outset). At the same time, if it encounters a region in the outset whoose
  refcount becomes 0 after the decrement, it calls free_region on that. This way we can be sure
  that all regions will eventually be garbage collected before the program exits.



Why is it a doubly linked-list?
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Due to way that bounds-checking works, the pointers in the outset may actually point to any
arbitrary chunk in the chain. However, we must call free_region on the first one to ensure that
all of them are GC'd. So we need pointers to traverse backward get to the first one.
'trav_to_first_chunk' accomplishes this.

 */

#define MAX_OUTSET_LENGTH 10

typedef struct RegionTy_struct {
    SymTy reg_id;
    uint reg_refcount;
    CursorTy reg_heap;
    uint reg_outset_len;
    CursorTy reg_outset[MAX_OUTSET_LENGTH];
} RegionTy;

typedef struct RegionFooter_struct {
    RegionTy *rf_reg_metadata_ptr;

    IntTy rf_seq_no;
    IntTy rf_size;
    struct RegionFooter_struct *rf_next;
    struct RegionFooter_struct *rf_prev;
} RegionFooter;

typedef struct ChunkTy_struct {
    CursorTy chunk_start;
    CursorTy chunk_end;
} ChunkTy;

static inline void insert_into_outset(CursorTy ptr, RegionTy *reg) {
    uint outset_len = reg->reg_outset_len;
    // Check for duplicates.
    for (uint i = 0; i < outset_len; i++) {
        if (ptr == reg->reg_outset[i]) {
            return;
        }
    }
    // Otherwise, insert into the outset.
    reg->reg_outset[outset_len] = ptr;
    reg->reg_outset_len = outset_len + 1;
    return;
}

static inline void remove_from_outset(CursorTy ptr, RegionTy *reg) {
    uint outset_len = reg->reg_outset_len;
    CursorTy *outset = reg->reg_outset;
    int i;
    if (outset_len == 0) {
        fprintf(stderr, "remove_from_outset: empty outset\n");
        exit(1);
    }
    // Position of 'ptr' in the outset.
    int elt_idx = -1;
    for (i = 0; i < outset_len; i++) {
        if (ptr == outset[i]) {
            elt_idx = i;
        }
    }
    if (elt_idx == -1) {
        fprintf(stderr, "remove_from_outset: element not found\n");
        exit(1);
    }
    // Move all elements ahead of 'elt_idx' back by one position.
    for (i = elt_idx; i < outset_len; i++) {
        outset[i] = outset[i+1];
    }
    return;
}

RegionTy *alloc_region(IntTy size) {
    // Allocate the region metadata.
    RegionTy *reg = ALLOC(sizeof(RegionTy));
    if (reg == NULL) {
        printf("alloc_region: allocation failed: %ld", sizeof(RegionTy));
        exit(1);
    }

    // Allocate the first chunk.
    IntTy total_size = size + sizeof(RegionFooter);
    CursorTy heap = ALLOC_PACKED_BIG(total_size);
    if (heap == NULL) {
        printf("alloc_region: malloc failed: %lld", total_size);
        exit(1);
    }
    // Not heap+total_size, since we must keep space for the footer.
    CursorTy heap_end = heap + size;

    // Initialize metadata fields.
    reg->reg_id = gensym();
    reg->reg_refcount = 1;
    reg->reg_heap = heap;
    reg->reg_outset_len = 0;

#ifdef _DEBUG
    printf("Allocated a region(%lld): %lld bytes.\n", reg->reg_id, size);
#endif

    // Write the footer.
    RegionFooter *footer = (RegionFooter *) heap_end;
    footer->rf_reg_metadata_ptr = reg;
    footer->rf_seq_no = 1;
    footer->rf_size = size;
    footer->rf_next = NULL;
    footer->rf_prev = NULL;

    return reg;
}

RegionTy *alloc_counted_region(IntTy size) {
    // Bump the count.
    bump_global_region_count();
    return alloc_region(size);
}

ChunkTy alloc_chunk(CursorTy end_old_chunk) {
    // Get size from current footer.
    RegionFooter *footer = (RegionFooter *) end_old_chunk;
    IntTy newsize = footer->rf_size * 2;
    // See #110.
    if (newsize > global_inf_buf_max_chunk_size) {
        newsize = global_inf_buf_max_chunk_size;
    }
    IntTy total_size = newsize + sizeof(RegionFooter);

    // Allocate.
    CursorTy start = ALLOC_PACKED_BIG(total_size);
    if (start == NULL) {
        printf("alloc_chunk: malloc failed: %lld", total_size);
        exit(1);
    }
    CursorTy end = start + newsize;

    // Link the next chunk's footer.
    footer->rf_next = (RegionFooter *) end;

    // Write the footer.
    RegionFooter* new_footer = (RegionFooter *) end;
    new_footer->rf_reg_metadata_ptr = footer->rf_reg_metadata_ptr;
    new_footer->rf_seq_no = footer->rf_seq_no + 1;
    new_footer->rf_size = newsize;
    new_footer->rf_next = NULL;
    new_footer->rf_prev = footer;

#ifdef _DEBUG
    RegionTy *reg = (RegionTy*) new_footer->rf_reg_metadata_ptr;
    printf("alloc_chunk: allocated %lld bytes for region %lld.\n", total_size, reg->reg_id);
#endif

    return (ChunkTy) {start , end};
}

RegionFooter* trav_to_first_chunk(RegionFooter *footer) {
    if (footer->rf_seq_no == 1) {
        return footer;
    } else if (footer->rf_prev == NULL) {
        fprintf(stderr, "No previous chunk found at rf_seq_no: %lld", footer->rf_seq_no);
        return NULL;
    } else {
        trav_to_first_chunk((RegionFooter *) footer->rf_prev);
    }
    return NULL;
}

uint get_ref_count(CursorTy end_ptr) {
    RegionFooter *footer = (RegionFooter *) end_ptr;
    RegionTy *reg = (RegionTy *) footer->rf_reg_metadata_ptr;
    return reg->reg_refcount;
}

// B is the pointer, and A is the pointee (i.e B -> A).
// Bump A's refcount and update B's outset.
static inline void bump_ref_count(CursorTy end_b, CursorTy end_a) {
    // Grab footers.
    RegionFooter *footer_a = (RegionFooter *) end_a;
    RegionFooter *footer_b = (RegionFooter *) end_b;

    // Grab metadata.
    RegionTy *reg_a = (RegionTy *) footer_a->rf_reg_metadata_ptr;
    RegionTy *reg_b = (RegionTy *) footer_b->rf_reg_metadata_ptr;

    // Bump A's refcount.
    uint current_refcount, new_refcount;
    current_refcount = reg_a->reg_refcount;
    new_refcount = current_refcount + 1;
    reg_a->reg_refcount = new_refcount;

#ifdef _DEBUG
    printf("bump_ref_count: %lld -> %lld\n", reg_b->reg_id, reg_a->reg_id);
    printf("bump_ref_count: old-refcount=%d, old-outset-len=%d:\n", current_refcount, reg_b->reg_outset_len);
    assert(current_refcount == reg_b->reg_outset_len+1);
#endif

    // Add A to B's outset.
    insert_into_outset(end_a, reg_b);

#ifdef _DEBUG
    // printf("bump_ref_count: Added %p to %lld's outset, %p.\n", end_a, reg_b->reg_id, reg_b);
    printf("bump_ref_count: new-refcount=%d, new-outset-len=%d\n", new_refcount, reg_b->reg_outset_len);
    assert(new_refcount == reg_b->reg_outset_len+1);
#endif

    return;
}

void free_region(CursorTy end_reg) {
    // Grab footer and the metadata.
    RegionFooter *footer = (RegionFooter *) end_reg;
    RegionTy *reg = (RegionTy *) footer->rf_reg_metadata_ptr;

    //
    RegionFooter *first_chunk_footer, *next_chunk_footer;
    CursorTy first_chunk, next_chunk;

    // Decrement current reference count.
    uint current_refcount, new_refcount;
    current_refcount = reg->reg_refcount;
    new_refcount = 0;
    if (current_refcount != 0) {
        new_refcount = current_refcount - 1;
        reg->reg_refcount = new_refcount;
    }

#ifdef _DEBUG
    printf("free_region(%lld): refcounts (1): old-refcount=%d, new-refcount=%d:\n", reg->reg_id, current_refcount, new_refcount);
#endif


    // Free this region recount is 0.
    if (new_refcount == 0) {

#ifdef _DEBUG
        printf("free_region(%lld): outset length: %d\n", reg->reg_id, reg->reg_outset_len);
#endif

        // Decrement refcounts, free regions with refcount==0 and also free
        // elements of the outset.
        if (reg->reg_outset_len != 0) {
            uint outset_len = reg->reg_outset_len;
            CursorTy *outset = reg->reg_outset;
            RegionFooter *elt_footer;
            RegionTy *elt_reg;
            uint elt_current_refcount, elt_new_refcount;
            CursorTy to_be_removed[MAX_OUTSET_LENGTH];
            uint to_be_removed_idx = 0;
            for (int i = 0; i < outset_len; i++) {
                elt_footer = (RegionFooter *) outset[i];
                elt_reg = (RegionTy *) elt_footer->rf_reg_metadata_ptr;
#ifdef _DEBUG
                elt_current_refcount = elt_reg->reg_refcount;
#endif
                elt_new_refcount = elt_current_refcount - 1;
                elt_reg->reg_refcount = elt_new_refcount;
#ifdef _DEBUG
                printf("free_region(%lld): old-refcount=%d, new-refcount=%d:\n",
                       elt_reg->reg_id, elt_current_refcount, elt_reg->reg_refcount);
#endif
                if (elt_new_refcount == 0) {
                    // See [Why is it a doubly linked-list?] above
                    first_chunk_footer = trav_to_first_chunk(elt_footer);
                    if (first_chunk_footer != NULL) {
                        free_region((CursorTy) first_chunk_footer);
                    }
                }
                to_be_removed[to_be_removed_idx] = outset[i];
                to_be_removed_idx++;
            }
            // Remove elements from the outset.
            for (uint i = 0; i < to_be_removed_idx; i++) {
                remove_from_outset(to_be_removed[i], reg);
            }
        }


#ifdef _DEBUG
        // Bookkeeping
        IntTy num_freed_chunks = 0, total_bytesize = 0;
#endif

        // Free the chunks in this region.
        first_chunk = end_reg - footer->rf_size;
        first_chunk_footer = footer;
        next_chunk = (char*) footer->rf_next;

#ifdef _DEBUG
        printf("free_region(%lld)\n", reg->reg_id);
#endif

#ifdef _DEBUG
        num_freed_chunks++;
        total_bytesize = total_bytesize + first_chunk_footer->rf_size;
#endif
        free(first_chunk);

        while (next_chunk != NULL) {
            next_chunk_footer = (RegionFooter *) next_chunk;
            #ifdef _DEBUG
            num_freed_chunks++;
            total_bytesize = total_bytesize + next_chunk_footer->rf_size;
            #endif
            free(next_chunk - next_chunk_footer->rf_size);
            next_chunk = (char*) next_chunk_footer->rf_next;
        }

#ifdef _DEBUG
        printf("free_region(%lld): Freed %lld bytes across %lld chunks.\n",
               reg->reg_id, total_bytesize, num_freed_chunks);
#endif

        // Free the metadata.
        free(reg);

    } else {
#ifdef _DEBUG
        printf("free_region(%lld): non-zero refcount: %d.\n",
               reg->reg_id, reg->reg_refcount);
#endif
    }
}

// Assume that all nodes with size information have tags >= 150.
BoolTy is_big(IntTy i, CursorTy cur) {
    TagTyPacked tag = *(TagTyPacked *) cur;
    if (tag >= 150) {
        cur += 1;
        IntTy size = *(IntTy *) cur;
        if (size >= i) {
            return true;
        } else {
            return false;
        }
    }
    return false;
}

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

// -------------------------------------
// Linked lists
// -------------------------------------

typedef struct ListTy_struct {
    IntTy ll_data_size;
    void* ll_data;
    struct ListTy_struct* ll_next;
} ListTy;

static inline ListTy* list_alloc(IntTy data_size) {
    // ListTy *ls = ALLOC(sizeof(ListTy));
    ListTy *ls = BUMPALLOC(sizeof(ListTy));
    ls->ll_data_size = data_size;
    ls->ll_data = NULL;
    ls->ll_next = NULL;
    return ls;
}

static inline BoolTy list_is_empty(ListTy *ls) {
    return ls->ll_next == NULL;
}

static inline ListTy* list_cons(void* elt, ListTy *ls) {
    // void* data = ALLOC(ls->data_size);
    void* data = BUMPALLOC(ls->ll_data_size);
    if (data == NULL) {
        printf("list_cons: malloc failed: %lld", ls->ll_data_size);
        exit(1);
    }
    memcpy(data, elt, ls->ll_data_size);
    // ListTy *res = ALLOC(sizeof(ListTy));
    ListTy *res = BUMPALLOC(sizeof(ListTy));
    res->ll_data_size = ls->ll_data_size;
    res->ll_data = data;
    res->ll_next = (ListTy*) ls;
    return res;
}

static inline void* list_head(ListTy *ls) {
    return ls->ll_data;
}

static inline ListTy* list_tail(ListTy *ls) {
    return ls->ll_next;
}

static inline void list_free(ListTy *ls) {
    free(ls->ll_data);
    free(ls);
    return;
}

static inline ListTy* list_copy(ListTy *ls) {
    ListTy *ls2 = list_alloc(ls->ll_data_size);
    if (ls->ll_data != NULL) {
        void* data = BUMPALLOC(ls->ll_data_size);
        memcpy(data, ls->ll_data, ls->ll_data_size);
        ls2->ll_data = data;
    }
    ls2->ll_next = ls->ll_next;
    return ls2;
}

// -------------------------------------
// Ppm Images
// -------------------------------------

typedef struct __Pixel_struct {
    IntTy field0;
    IntTy field1;
    IntTy field2;
} __Pixel;

void writePpm(char* filename, IntTy width, IntTy height, VectorTy *pixels);
void writePpm_loop(FILE *fp, IntTy idx, IntTy end, VectorTy *pixels);

// Example: writePpm("gibbon_rgb_1000.ppm", 1000, 1000, pixels);
void writePpm(char* filename, IntTy width, IntTy height, VectorTy *pixels)
{
    FILE *fp;
    fp = fopen(filename, "w+");
    fprintf(fp, "P3\n");
    fprintf(fp, "%lld %lld\n255\n", width, height);
    IntTy len = vector_length(pixels);
    writePpm_loop(fp, 0, len, pixels);
    fclose(fp);
    return;
}

void writePpm_loop(FILE *fp, IntTy idx, IntTy end, VectorTy *pixels)
{
    BoolTy fltIf_5768_6575 = idx == end;

    if (fltIf_5768_6575) {
        return;
    } else {
        __Pixel *tmp_112;
        tmp_112 = (__Pixel *) vector_nth(pixels, idx);
        __Pixel tup = *tmp_112;
        IntTy x = tup.field0;
        IntTy y = tup.field1;
        IntTy z = tup.field2;
        // write to file.
        fprintf(fp, "%lld %lld %lld\n", x, y, z);
        writePpm_loop(fp, (idx+1), end, pixels);
    }
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
typedef struct Float32Prod_struct {
            FloatTy field0;
        } Float32Prod;
typedef struct BoolProd_struct {
            BoolTy field0;
        } BoolProd;
typedef struct VectorProd_struct {
            VectorTy *field0;
        } VectorProd;
unsigned char bench_main();
unsigned char print_check(BoolTy b_418_2437_3280);
IntTy compare_float_original(FloatTy r1_434_2442_3283,
                             FloatTy r2_435_2443_3284);
int compare_float(const void *r1_434_2442_3283, const void *r2_435_2443_3284);
IntTy maxInt(IntTy a_436_2444_3287, IntTy b_437_2445_3288);
IntTy minInt(IntTy a_444_2452_3290, IntTy b_445_2453_3291);
IntTy defaultGrainSize(IntTy n_633_2454_3293);
VectorTy *write_loop_1280(IntTy to_idx_345_2457_3298,
                          IntTy from_idx_346_2458_3299, IntTy end_347_2459_3300,
                          VectorTy *from_348_2460_3301,
                          VectorTy *to_349_2461_3302);
VectorTy *write_loop_seq_1260(IntTy to_idx_355_2504_3312,
                              IntTy from_idx_356_2505_3313,
                              IntTy end_357_2506_3314,
                              VectorTy *from_358_2507_3315,
                              VectorTy *to_359_2508_3316);
VectorTy *generate_par_loop_1253_2160(IntTy cutoff_745_2558_3343,
                                      VectorTy *vec_746_2559_3344,
                                      IntTy start_747_2560_3345,
                                      IntTy end_748_2561_3346,
                                      VectorTy *vec_412_2562_3347);
VectorTy *generate_loop_1251_2161(VectorTy *vec_579_2567_3355,
                                  IntTy idx_580_2568_3356,
                                  IntTy end_581_2569_3357,
                                  VectorTy *vec_412_2570_3358);
VectorTy *generate_loop_1251_2164(VectorTy *vec_579_2590_3365,
                                  IntTy idx_580_2591_3366,
                                  IntTy end_581_2592_3367);
VectorTy *generate_loop_1251_2165(VectorTy *vec_579_2598_3374,
                                  IntTy idx_580_2599_3375,
                                  IntTy end_581_2600_3376);
VectorTy *generate_loop_1251_2166(VectorTy *vec_579_2602_3383,
                                  IntTy idx_580_2603_3384,
                                  IntTy end_581_2604_3385,
                                  VectorTy *vec_415_2605_3386);
VectorTy *writeSort1_1277_2171(VectorTy *src_285_2634_3398,
                               VectorTy *tmp_286_2635_3399);
VectorTy *writeMerge_1279_2174(VectorTy *src_1_301_2648_3433,
                               VectorTy *src_2_302_2649_3434,
                               VectorTy *tmp_303_2650_3435);
IntTy binarySearch__1282_2177(IntTy lo_366_2669_3495, IntTy hi_367_2670_3496,
                              VectorTy *vec_369_2671_3497,
                              FloatTy query_370_2672_3498);
VectorTy *writeSort2_1278_2173(VectorTy *src_253_2677_3514,
                               VectorTy *tmp_254_2678_3515);
VectorTy *writeMerge_seq_loop_1261_2178(IntTy i1_329_2699_3550,
                                        IntTy i2_330_2700_3551,
                                        IntTy j_331_2701_3552,
                                        IntTy n1_332_2702_3553,
                                        IntTy n2_333_2703_3554,
                                        VectorTy *src_1_335_2704_3555,
                                        VectorTy *src_2_336_2705_3556,
                                        VectorTy *tmp_337_2706_3557);
VectorTy *writeSort1_seq_1255_2189(VectorTy *src_270_2804_3591,
                                   VectorTy *tmp_271_2805_3592);
VectorTy *writeSort2_seq_1258_2190(VectorTy *src_237_2817_3631,
                                   VectorTy *tmp_238_2818_3632);
unsigned char check_sorted_1227_2143(VectorTy *sorted_207_2839_3672);
BoolTy ifoldl_loop_1249_2193(IntTy idx_503_2843_3686, IntTy end_504_2844_3687,
                             BoolTy acc_506_2845_3688,
                             VectorTy *vec_507_2846_3689,
                             VectorTy *arr1_210_2847_3690);
unsigned char bench_main()
{
    BoolTy fltIf_3166_3259 = strcmp("seqmergesort", global_bench_prog_param) ==
           0;
    
    if (fltIf_3166_3259) {
        IntTy n_190_2423_3260 = global_size_param;
        IntTy n__431_2587_2850_3262 =  maxInt(n_190_2423_3260, 0);
        IntTy tmp_7 = sizeof(FloatTy);
        VectorTy *vec_432_2588_2851_3263 = vector_alloc(n__431_2587_2850_3262,
                                                        tmp_7);
        VectorTy *vec1_433_2589_2852_3264 =
                  generate_loop_1251_2164(vec_432_2588_2851_3263, 0, n__431_2587_2850_3262);
        VectorTy *timed_3785;
        VectorTy *times_5 = vector_alloc(global_iters_param, sizeof(double));
        struct timespec begin_timed_3785;
        struct timespec end_timed_3785;
        
        for (long long iters_timed_3785 = 0; iters_timed_3785 <
             global_iters_param; iters_timed_3785++) {
            if (iters_timed_3785 != global_iters_param - 1)
                save_alloc_state();
            clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_3785);
            
            IntTy n_428_2537_2883_3327_3703 =
                  vector_length(vec1_433_2589_2852_3264);
            IntTy n__431_2539_2885_3329_3705 =
                   maxInt(n_428_2537_2883_3327_3703, 0);
            IntTy tmp_1 = sizeof(FloatTy);
            VectorTy *vec_432_2540_2886_3330_3706 =
                     vector_alloc(n__431_2539_2885_3329_3705, tmp_1);
            VectorTy *vec1_433_2541_2887_3331_3707 =
                      generate_loop_1251_2166(vec_432_2540_2886_3330_3706, 0, n__431_2539_2885_3329_3705, vec1_433_2589_2852_3264);
            IntTy vec_410_2494_3109_3588_3710 =
                  vector_length(vec1_433_2541_2887_3331_3707);
            IntTy tmp_0 = sizeof(FloatTy);
            VectorTy *tmp_229_2802_3589_3711 =
                     vector_alloc(vec_410_2494_3109_3588_3710, tmp_0);
            VectorTy *tmp2_230_2803_3590_3712 =
                      writeSort1_seq_1255_2189(vec1_433_2541_2887_3331_3707, tmp_229_2802_3589_3711);
            
            timed_3785 = vec1_433_2541_2887_3331_3707;
            clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_3785);
            if (iters_timed_3785 != global_iters_param - 1)
                restore_alloc_state();
            
            double itertime_2 = difftimespecs(&begin_timed_3785,
                                              &end_timed_3785);
            
            vector_inplace_update(times_5, iters_timed_3785, &itertime_2);
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
        
        unsigned char tailapp_3757 =  check_sorted_1227_2143(timed_3785);
        
        return tailapp_3757;
    } else {
        IntTy n_194_2426_3270 = global_size_param;
        IntTy n__431_2595_2857_3272 =  maxInt(n_194_2426_3270, 0);
        IntTy tmp_15 = sizeof(FloatTy);
        VectorTy *vec_432_2596_2858_3273 = vector_alloc(n__431_2595_2857_3272,
                                                        tmp_15);
        VectorTy *vec1_433_2597_2859_3274 =
                  generate_loop_1251_2165(vec_432_2596_2858_3273, 0, n__431_2595_2857_3272);
        VectorTy *timed_3786;
        VectorTy *times_13 = vector_alloc(global_iters_param, sizeof(double));
        struct timespec begin_timed_3786;
        struct timespec end_timed_3786;
        
        for (long long iters_timed_3786 = 0; iters_timed_3786 <
             global_iters_param; iters_timed_3786++) {
            if (iters_timed_3786 != global_iters_param - 1)
                save_alloc_state();
            clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_3786);
            
            IntTy n_738_2544_2889_3334_3715 =
                  vector_length(vec1_433_2597_2859_3274);
            IntTy n__741_2546_2891_3336_3717 =
                   maxInt(n_738_2544_2889_3334_3715, 0);
            IntTy tmp_9 = sizeof(FloatTy);
            VectorTy *vec_742_2547_2892_3337_3718 =
                     vector_alloc(n__741_2546_2891_3336_3717, tmp_9);
            IntTy cutoff_743_2548_2893_3338_3719 =
                   defaultGrainSize(n__741_2546_2891_3336_3717);
            VectorTy *vec1_744_2549_2894_3339_3720 =
                      generate_par_loop_1253_2160(cutoff_743_2548_2893_3338_3719, vec_742_2547_2892_3337_3718, 0, n__741_2546_2891_3336_3717, vec1_433_2597_2859_3274);
            IntTy vec_410_2494_2933_3395_3723 =
                  vector_length(vec1_744_2549_2894_3339_3720);
            IntTy tmp_8 = sizeof(FloatTy);
            VectorTy *tmp_234_2632_3396_3724 =
                     vector_alloc(vec_410_2494_2933_3395_3723, tmp_8);
            VectorTy *tmp2_235_2633_3397_3725 =
                      writeSort1_1277_2171(vec1_744_2549_2894_3339_3720, tmp_234_2632_3396_3724);
            
            timed_3786 = vec1_744_2549_2894_3339_3720;
            clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_3786);
            if (iters_timed_3786 != global_iters_param - 1)
                restore_alloc_state();
            
            double itertime_10 = difftimespecs(&begin_timed_3786,
                                               &end_timed_3786);
            
            vector_inplace_update(times_13, iters_timed_3786, &itertime_10);
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
        
        unsigned char tailapp_3758 =  check_sorted_1227_2143(timed_3786);
        
        return tailapp_3758;
    }
}
unsigned char print_check(BoolTy b_418_2437_3280)
{
    if (b_418_2437_3280) {
        unsigned char wildcard__14_419_2438_3281 = print_symbol(3787);
        
        return 0;
    } else {
        unsigned char wildcard__16_420_2439_3282 = print_symbol(3788);
        
        return 0;
    }
}
IntTy compare_float_original(FloatTy r1_434_2442_3283, FloatTy r2_435_2443_3284)
{
    BoolTy fltIf_3167_3285 = r1_434_2442_3283 < r2_435_2443_3284;
    
    if (fltIf_3167_3285) {
        IntTy tailprim_3763 = 0 - 1;
        
        return tailprim_3763;
    } else {
        BoolTy fltIf_3168_3286 = r1_434_2442_3283 > r2_435_2443_3284;
        
        if (fltIf_3168_3286) {
            return 1;
        } else {
            return 0;
        }
    }
}
int compare_float(const void *r1_434_2442_3283, const void *r2_435_2443_3284)
{
    FloatTy fst_16 = *(FloatTy *) r1_434_2442_3283;
    FloatTy snd_17 = *(FloatTy *) r2_435_2443_3284;
    
    return compare_float_original(fst_16, snd_17);
}
IntTy maxInt(IntTy a_436_2444_3287, IntTy b_437_2445_3288)
{
    BoolTy fltIf_3169_3289 = a_436_2444_3287 > b_437_2445_3288;
    
    if (fltIf_3169_3289) {
        return a_436_2444_3287;
    } else {
        return b_437_2445_3288;
    }
}
IntTy minInt(IntTy a_444_2452_3290, IntTy b_445_2453_3291)
{
    BoolTy fltIf_3170_3292 = a_444_2452_3290 < b_445_2453_3291;
    
    if (fltIf_3170_3292) {
        return a_444_2452_3290;
    } else {
        return b_445_2453_3291;
    }
}
IntTy defaultGrainSize(IntTy n_633_2454_3293)
{
    IntTy p_634_2455_3294 = get_num_processors();
    IntTy fltPrm_3172_3295 = 8 * p_634_2455_3294;
    IntTy fltAppE_3171_3296 = n_633_2454_3293 / fltPrm_3172_3295;
    IntTy grain_635_2456_3297 =  maxInt(1, fltAppE_3171_3296);
    IntTy tailapp_3764 =  minInt(2048, grain_635_2456_3297);
    
    return tailapp_3764;
}
VectorTy *write_loop_1280(IntTy to_idx_345_2457_3298,
                          IntTy from_idx_346_2458_3299, IntTy end_347_2459_3300,
                          VectorTy *from_348_2460_3301,
                          VectorTy *to_349_2461_3302)
{
    IntTy fltPrm_3174_3303 = end_347_2459_3300 - from_idx_346_2458_3299;
    BoolTy fltIf_3173_3304 = fltPrm_3174_3303 < 4096;
    
    if (fltIf_3173_3304) {
        VectorTy *tailapp_3765 =
                  write_loop_seq_1260(to_idx_345_2457_3298, from_idx_346_2458_3299, end_347_2459_3300, from_348_2460_3301, to_349_2461_3302);
        
        return tailapp_3765;
    } else {
        IntTy fltPrm_3175_3305 = from_idx_346_2458_3299 + end_347_2459_3300;
        IntTy mid_351_2462_3306 = fltPrm_3175_3305 / 2;
        IntTy parent_id_3752 = __cilkrts_get_worker_number();
        VectorTy *to1_352_2463_3307 =
                 cilk_spawn write_loop_1280(to_idx_345_2457_3298, from_idx_346_2458_3299, mid_351_2462_3306, from_348_2460_3301, to_349_2461_3302);
        IntTy fltPrm_3177_3308 = to_idx_345_2457_3298 + mid_351_2462_3306;
        IntTy fltAppE_3176_3309 = fltPrm_3177_3308 - from_idx_346_2458_3299;
        VectorTy *to2_353_2464_3310 =
                  write_loop_1280(fltAppE_3176_3309, mid_351_2462_3306, end_347_2459_3300, from_348_2460_3301, to_349_2461_3302);
        
        cilk_sync;
        return to2_353_2464_3310;
    }
}
VectorTy *write_loop_seq_1260(IntTy to_idx_355_2504_3312,
                              IntTy from_idx_356_2505_3313,
                              IntTy end_357_2506_3314,
                              VectorTy *from_358_2507_3315,
                              VectorTy *to_359_2508_3316)
{
    BoolTy fltIf_3178_3317 = from_idx_356_2505_3313 == end_357_2506_3314;
    
    if (fltIf_3178_3317) {
        return to_359_2508_3316;
    } else {
        FloatTy *tmp_18;
        
        tmp_18 = (FloatTy *) vector_nth(from_358_2507_3315,
                                        from_idx_356_2505_3313);
        
        FloatTy val_393_2502_2881_3321 = *tmp_18;
        VectorTy *to1_361_2509_3323 = vector_inplace_update(to_359_2508_3316,
                                                            to_idx_355_2504_3312,
                                                            &val_393_2502_2881_3321);
        IntTy fltAppE_3179_3324 = to_idx_355_2504_3312 + 1;
        IntTy fltAppE_3180_3325 = from_idx_356_2505_3313 + 1;
        VectorTy *tailapp_3766 =
                  write_loop_seq_1260(fltAppE_3179_3324, fltAppE_3180_3325, end_357_2506_3314, from_358_2507_3315, to1_361_2509_3323);
        
        return tailapp_3766;
    }
}
VectorTy *generate_par_loop_1253_2160(IntTy cutoff_745_2558_3343,
                                      VectorTy *vec_746_2559_3344,
                                      IntTy start_747_2560_3345,
                                      IntTy end_748_2561_3346,
                                      VectorTy *vec_412_2562_3347)
{
    IntTy fltPrm_3182_3348 = end_748_2561_3346 - start_747_2560_3345;
    BoolTy fltIf_3181_3349 = fltPrm_3182_3348 <= cutoff_745_2558_3343;
    
    if (fltIf_3181_3349) {
        VectorTy *tailapp_3767 =
                  generate_loop_1251_2161(vec_746_2559_3344, start_747_2560_3345, end_748_2561_3346, vec_412_2562_3347);
        
        return tailapp_3767;
    } else {
        IntTy fltPrm_3183_3350 = start_747_2560_3345 + end_748_2561_3346;
        IntTy mid_751_2563_3351 = fltPrm_3183_3350 / 2;
        IntTy parent_id_3753 = __cilkrts_get_worker_number();
        VectorTy *_vec1_752_2564_3352 =
                 cilk_spawn generate_par_loop_1253_2160(cutoff_745_2558_3343, vec_746_2559_3344, start_747_2560_3345, mid_751_2563_3351, vec_412_2562_3347);
        VectorTy *vec2_753_2565_3353 =
                  generate_par_loop_1253_2160(cutoff_745_2558_3343, vec_746_2559_3344, mid_751_2563_3351, end_748_2561_3346, vec_412_2562_3347);
        
        cilk_sync;
        return vec2_753_2565_3353;
    }
}
VectorTy *generate_loop_1251_2161(VectorTy *vec_579_2567_3355,
                                  IntTy idx_580_2568_3356,
                                  IntTy end_581_2569_3357,
                                  VectorTy *vec_412_2570_3358)
{
    BoolTy fltIf_3184_3359 = idx_580_2568_3356 == end_581_2569_3357;
    
    if (fltIf_3184_3359) {
        return vec_579_2567_3355;
    } else {
        FloatTy *tmp_19;
        
        tmp_19 = (FloatTy *) vector_nth(vec_412_2570_3358, idx_580_2568_3356);
        
        FloatTy fltPrm_3185_3362 = *tmp_19;
        VectorTy *vec1_584_2571_3363 = vector_inplace_update(vec_579_2567_3355,
                                                             idx_580_2568_3356,
                                                             &fltPrm_3185_3362);
        IntTy fltAppE_3186_3364 = idx_580_2568_3356 + 1;
        VectorTy *tailapp_3768 =
                  generate_loop_1251_2161(vec1_584_2571_3363, fltAppE_3186_3364, end_581_2569_3357, vec_412_2570_3358);
        
        return tailapp_3768;
    }
}
VectorTy *generate_loop_1251_2164(VectorTy *vec_579_2590_3365,
                                  IntTy idx_580_2591_3366,
                                  IntTy end_581_2592_3367)
{
    BoolTy fltIf_3187_3368 = idx_580_2591_3366 == end_581_2592_3367;
    
    if (fltIf_3187_3368) {
        return vec_579_2590_3365;
    } else {
        IntTy fltPrm_3189_3370 = rand();
        FloatTy fltPrm_3188_3371 = (FloatTy) fltPrm_3189_3370;
        VectorTy *vec1_584_2593_3372 = vector_inplace_update(vec_579_2590_3365,
                                                             idx_580_2591_3366,
                                                             &fltPrm_3188_3371);
        IntTy fltAppE_3190_3373 = idx_580_2591_3366 + 1;
        VectorTy *tailapp_3769 =
                  generate_loop_1251_2164(vec1_584_2593_3372, fltAppE_3190_3373, end_581_2592_3367);
        
        return tailapp_3769;
    }
}
VectorTy *generate_loop_1251_2165(VectorTy *vec_579_2598_3374,
                                  IntTy idx_580_2599_3375,
                                  IntTy end_581_2600_3376)
{
    BoolTy fltIf_3191_3377 = idx_580_2599_3375 == end_581_2600_3376;
    
    if (fltIf_3191_3377) {
        return vec_579_2598_3374;
    } else {
        IntTy fltPrm_3193_3379 = rand();
        FloatTy fltPrm_3192_3380 = (FloatTy) fltPrm_3193_3379;
        VectorTy *vec1_584_2601_3381 = vector_inplace_update(vec_579_2598_3374,
                                                             idx_580_2599_3375,
                                                             &fltPrm_3192_3380);
        IntTy fltAppE_3194_3382 = idx_580_2599_3375 + 1;
        VectorTy *tailapp_3770 =
                  generate_loop_1251_2165(vec1_584_2601_3381, fltAppE_3194_3382, end_581_2600_3376);
        
        return tailapp_3770;
    }
}
VectorTy *generate_loop_1251_2166(VectorTy *vec_579_2602_3383,
                                  IntTy idx_580_2603_3384,
                                  IntTy end_581_2604_3385,
                                  VectorTy *vec_415_2605_3386)
{
    BoolTy fltIf_3195_3387 = idx_580_2603_3384 == end_581_2604_3385;
    
    if (fltIf_3195_3387) {
        return vec_579_2602_3383;
    } else {
        FloatTy *tmp_20;
        
        tmp_20 = (FloatTy *) vector_nth(vec_415_2605_3386, idx_580_2603_3384);
        
        FloatTy fltPrm_3196_3390 = *tmp_20;
        VectorTy *vec1_584_2606_3391 = vector_inplace_update(vec_579_2602_3383,
                                                             idx_580_2603_3384,
                                                             &fltPrm_3196_3390);
        IntTy fltAppE_3197_3392 = idx_580_2603_3384 + 1;
        VectorTy *tailapp_3771 =
                  generate_loop_1251_2166(vec1_584_2606_3391, fltAppE_3197_3392, end_581_2604_3385, vec_415_2605_3386);
        
        return tailapp_3771;
    }
}
VectorTy *writeSort1_1277_2171(VectorTy *src_285_2634_3398,
                               VectorTy *tmp_286_2635_3399)
{
    IntTy len_288_2636_3401 = vector_length(src_285_2634_3398);
    BoolTy fltIf_3198_3402 = len_288_2636_3401 < 8192;
    
    if (fltIf_3198_3402) {
        VectorTy *tailprim_3772 = vector_inplace_sort(src_285_2634_3398,
                                                      compare_float);
        
        return tailprim_3772;
    } else {
        IntTy half_289_2637_3404 = len_288_2636_3401 / 2;
        IntTy len_406_2497_2938_3407 = vector_length(src_285_2634_3398);
        IntTy n__407_2498_2939_3408 =  maxInt(half_289_2637_3404, 0);
        IntTy m_408_2499_2940_3409 =
               minInt(n__407_2498_2939_3408, len_406_2497_2938_3407);
        IntTy fltAppE_3199_3410 = len_406_2497_2938_3407 -
              n__407_2498_2939_3408;
        IntTy m__409_2500_2941_3411 =  maxInt(0, fltAppE_3199_3410);
        VectorTy *fltPrd_3200_3412 = vector_slice(0, m_408_2499_2940_3409,
                                                  src_285_2634_3398);
        VectorTy *fltPrd_3201_3413 = vector_slice(m_408_2499_2940_3409,
                                                  m__409_2500_2941_3411,
                                                  src_285_2634_3398);
        IntTy len_406_2497_2944_3419 = vector_length(tmp_286_2635_3399);
        IntTy n__407_2498_2945_3420 =  maxInt(half_289_2637_3404, 0);
        IntTy m_408_2499_2946_3421 =
               minInt(n__407_2498_2945_3420, len_406_2497_2944_3419);
        IntTy fltAppE_3202_3422 = len_406_2497_2944_3419 -
              n__407_2498_2945_3420;
        IntTy m__409_2500_2947_3423 =  maxInt(0, fltAppE_3202_3422);
        VectorTy *fltPrd_3203_3424 = vector_slice(0, m_408_2499_2946_3421,
                                                  tmp_286_2635_3399);
        VectorTy *fltPrd_3204_3425 = vector_slice(m_408_2499_2946_3421,
                                                  m__409_2500_2947_3423,
                                                  tmp_286_2635_3399);
        IntTy parent_id_3754 = __cilkrts_get_worker_number();
        VectorTy *tmp_l1_296_2644_3429 =
                 cilk_spawn writeSort2_1278_2173(fltPrd_3200_3412, fltPrd_3203_3424);
        VectorTy *tmp_r1_297_2645_3430 =
                  writeSort2_1278_2173(fltPrd_3201_3413, fltPrd_3204_3425);
        
        cilk_sync;
        
        VectorTy *res_299_2647_3432 =
                  writeMerge_1279_2174(tmp_l1_296_2644_3429, tmp_r1_297_2645_3430, src_285_2634_3398);
        
        return res_299_2647_3432;
    }
}
VectorTy *writeMerge_1279_2174(VectorTy *src_1_301_2648_3433,
                               VectorTy *src_2_302_2649_3434,
                               VectorTy *tmp_303_2650_3435)
{
    IntTy fltPrm_3206_3437 = vector_length(tmp_303_2650_3435);
    BoolTy fltIf_3205_3438 = fltPrm_3206_3437 < 4096;
    
    if (fltIf_3205_3438) {
        IntTy n1_326_2696_2952_3442 = vector_length(src_1_301_2648_3433);
        IntTy n2_327_2697_2953_3443 = vector_length(src_2_302_2649_3434);
        VectorTy *res_328_2698_2954_3444 =
                  writeMerge_seq_loop_1261_2178(0, 0, 0, n1_326_2696_2952_3442, n2_327_2697_2953_3443, src_1_301_2648_3433, src_2_302_2649_3434, tmp_303_2650_3435);
        
        return res_328_2698_2954_3444;
    } else {
        IntTy n1_305_2651_3446 = vector_length(src_1_301_2648_3433);
        IntTy n2_306_2652_3448 = vector_length(src_2_302_2649_3434);
        BoolTy fltIf_3207_3449 = n1_305_2651_3446 == 0;
        
        if (fltIf_3207_3449) {
            VectorTy *tailapp_3773 =
                      write_loop_1280(0, 0, n2_306_2652_3448, src_2_302_2649_3434, tmp_303_2650_3435);
            
            return tailapp_3773;
        } else {
            IntTy mid1_307_2653_3450 = n1_305_2651_3446 / 2;
            FloatTy *tmp_21;
            
            tmp_21 = (FloatTy *) vector_nth(src_1_301_2648_3433,
                                            mid1_307_2653_3450);
            
            FloatTy pivot_308_2654_3453 = *tmp_21;
            IntTy fltAppE_3208_3456 = vector_length(src_2_302_2649_3434);
            IntTy mid2_309_2655_3457 =
                   binarySearch__1282_2177(0, fltAppE_3208_3456, src_2_302_2649_3434, pivot_308_2654_3453);
            VectorTy *src_1_l_310_2656_3461 = vector_slice(0,
                                                           mid1_307_2653_3450,
                                                           src_1_301_2648_3433);
            IntTy i_396_2516_2964_3462 = mid1_307_2653_3450 + 1;
            IntTy fltPrm_3209_3463 = mid1_307_2653_3450 + 1;
            IntTy n_397_2517_2965_3464 = n1_305_2651_3446 - fltPrm_3209_3463;
            VectorTy *src_1_r_311_2657_3466 = vector_slice(i_396_2516_2964_3462,
                                                           n_397_2517_2965_3464,
                                                           src_1_301_2648_3433);
            VectorTy *src_2_l_312_2658_3470 = vector_slice(0,
                                                           mid2_309_2655_3457,
                                                           src_2_302_2649_3434);
            IntTy n_397_2517_2971_3472 = n2_306_2652_3448 - mid2_309_2655_3457;
            VectorTy *src_2_r_313_2659_3474 = vector_slice(mid2_309_2655_3457,
                                                           n_397_2517_2971_3472,
                                                           src_2_302_2649_3434);
            IntTy i_392_2501_2973_3475 = mid1_307_2653_3450 +
                  mid2_309_2655_3457;
            VectorTy *wildcard__67_314_2660_3478 =
                     vector_inplace_update(tmp_303_2650_3435,
                                           i_392_2501_2973_3475,
                                           &pivot_308_2654_3453);
            IntTy len_t_315_2661_3480 = vector_length(tmp_303_2650_3435);
            IntTy n_397_2517_2978_3482 = mid1_307_2653_3450 +
                  mid2_309_2655_3457;
            VectorTy *tmp_l_316_2662_3484 = vector_slice(0,
                                                         n_397_2517_2978_3482,
                                                         tmp_303_2650_3435);
            IntTy fltPrm_3210_3485 = mid1_307_2653_3450 + mid2_309_2655_3457;
            IntTy i_396_2516_2980_3486 = fltPrm_3210_3485 + 1;
            IntTy fltPrm_3212_3487 = mid1_307_2653_3450 + mid2_309_2655_3457;
            IntTy fltPrm_3211_3488 = fltPrm_3212_3487 + 1;
            IntTy n_397_2517_2981_3489 = len_t_315_2661_3480 - fltPrm_3211_3488;
            VectorTy *tmp_r_317_2663_3491 = vector_slice(i_396_2516_2980_3486,
                                                         n_397_2517_2981_3489,
                                                         tmp_303_2650_3435);
            IntTy parent_id_3755 = __cilkrts_get_worker_number();
            VectorTy *tmp_l1_318_2664_3492 =
                     cilk_spawn writeMerge_1279_2174(src_1_l_310_2656_3461, src_2_l_312_2658_3470, tmp_l_316_2662_3484);
            VectorTy *tmp_r1_319_2665_3493 =
                      writeMerge_1279_2174(src_1_r_311_2657_3466, src_2_r_313_2659_3474, tmp_r_317_2663_3491);
            
            cilk_sync;
            return tmp_303_2650_3435;
        }
    }
}
IntTy binarySearch__1282_2177(IntTy lo_366_2669_3495, IntTy hi_367_2670_3496,
                              VectorTy *vec_369_2671_3497,
                              FloatTy query_370_2672_3498)
{
    IntTy n_372_2673_3499 = hi_367_2670_3496 - lo_366_2669_3495;
    BoolTy fltIf_3213_3500 = n_372_2673_3499 == 0;
    
    if (fltIf_3213_3500) {
        return lo_366_2669_3495;
    } else {
        IntTy fltPrm_3214_3501 = n_372_2673_3499 / 2;
        IntTy mid_373_2674_3502 = lo_366_2669_3495 + fltPrm_3214_3501;
        FloatTy *tmp_22;
        
        tmp_22 = (FloatTy *) vector_nth(vec_369_2671_3497, mid_373_2674_3502);
        
        FloatTy pivot_374_2675_3505 = *tmp_22;
        BoolTy fltIf_3215_3508 = query_370_2672_3498 < pivot_374_2675_3505;
        IntTy tst_375_2676_3510;
        
        if (fltIf_3215_3508) {
            IntTy flt_3793 = 0 - 1;
            
            tst_375_2676_3510 = flt_3793;
        } else {
            BoolTy fltIf_3216_3509 = query_370_2672_3498 > pivot_374_2675_3505;
            
            if (fltIf_3216_3509) {
                tst_375_2676_3510 = 1;
            } else {
                tst_375_2676_3510 = 0;
            }
        }
        
        BoolTy fltIf_3217_3511 = tst_375_2676_3510 < 0;
        
        if (fltIf_3217_3511) {
            IntTy tailapp_3774 =
                   binarySearch__1282_2177(lo_366_2669_3495, mid_373_2674_3502, vec_369_2671_3497, query_370_2672_3498);
            
            return tailapp_3774;
        } else {
            BoolTy fltIf_3218_3512 = tst_375_2676_3510 > 0;
            
            if (fltIf_3218_3512) {
                IntTy fltAppE_3219_3513 = mid_373_2674_3502 + 1;
                IntTy tailapp_3775 =
                       binarySearch__1282_2177(fltAppE_3219_3513, hi_367_2670_3496, vec_369_2671_3497, query_370_2672_3498);
                
                return tailapp_3775;
            } else {
                return mid_373_2674_3502;
            }
        }
    }
}
VectorTy *writeSort2_1278_2173(VectorTy *src_253_2677_3514,
                               VectorTy *tmp_254_2678_3515)
{
    IntTy len_256_2679_3517 = vector_length(src_253_2677_3514);
    BoolTy fltIf_3220_3518 = len_256_2679_3517 < 8192;
    
    if (fltIf_3220_3518) {
        VectorTy *tmp_1_257_2680_3519 =
                  write_loop_1280(0, 0, len_256_2679_3517, src_253_2677_3514, tmp_254_2678_3515);
        VectorTy *tailprim_3776 = vector_inplace_sort(tmp_1_257_2680_3519,
                                                      compare_float);
        
        return tailprim_3776;
    } else {
        IntTy half_258_2681_3521 = len_256_2679_3517 / 2;
        IntTy len_406_2497_2992_3524 = vector_length(src_253_2677_3514);
        IntTy n__407_2498_2993_3525 =  maxInt(half_258_2681_3521, 0);
        IntTy m_408_2499_2994_3526 =
               minInt(n__407_2498_2993_3525, len_406_2497_2992_3524);
        IntTy fltAppE_3221_3527 = len_406_2497_2992_3524 -
              n__407_2498_2993_3525;
        IntTy m__409_2500_2995_3528 =  maxInt(0, fltAppE_3221_3527);
        VectorTy *fltPrd_3222_3529 = vector_slice(0, m_408_2499_2994_3526,
                                                  src_253_2677_3514);
        VectorTy *fltPrd_3223_3530 = vector_slice(m_408_2499_2994_3526,
                                                  m__409_2500_2995_3528,
                                                  src_253_2677_3514);
        IntTy len_406_2497_2998_3536 = vector_length(tmp_254_2678_3515);
        IntTy n__407_2498_2999_3537 =  maxInt(half_258_2681_3521, 0);
        IntTy m_408_2499_3000_3538 =
               minInt(n__407_2498_2999_3537, len_406_2497_2998_3536);
        IntTy fltAppE_3224_3539 = len_406_2497_2998_3536 -
              n__407_2498_2999_3537;
        IntTy m__409_2500_3001_3540 =  maxInt(0, fltAppE_3224_3539);
        VectorTy *fltPrd_3225_3541 = vector_slice(0, m_408_2499_3000_3538,
                                                  tmp_254_2678_3515);
        VectorTy *fltPrd_3226_3542 = vector_slice(m_408_2499_3000_3538,
                                                  m__409_2500_3001_3540,
                                                  tmp_254_2678_3515);
        IntTy parent_id_3756 = __cilkrts_get_worker_number();
        VectorTy *src_l1_265_2688_3546 =
                 cilk_spawn writeSort1_1277_2171(fltPrd_3222_3529, fltPrd_3225_3541);
        VectorTy *src_r1_266_2689_3547 =
                  writeSort1_1277_2171(fltPrd_3223_3530, fltPrd_3226_3542);
        
        cilk_sync;
        
        VectorTy *res_268_2691_3549 =
                  writeMerge_1279_2174(src_l1_265_2688_3546, src_r1_266_2689_3547, tmp_254_2678_3515);
        
        return res_268_2691_3549;
    }
}
VectorTy *writeMerge_seq_loop_1261_2178(IntTy i1_329_2699_3550,
                                        IntTy i2_330_2700_3551,
                                        IntTy j_331_2701_3552,
                                        IntTy n1_332_2702_3553,
                                        IntTy n2_333_2703_3554,
                                        VectorTy *src_1_335_2704_3555,
                                        VectorTy *src_2_336_2705_3556,
                                        VectorTy *tmp_337_2706_3557)
{
    BoolTy fltIf_3227_3558 = i1_329_2699_3550 == n1_332_2702_3553;
    
    if (fltIf_3227_3558) {
        VectorTy *tmp_2_339_2707_3559 =
                  write_loop_seq_1260(j_331_2701_3552, i2_330_2700_3551, n2_333_2703_3554, src_2_336_2705_3556, tmp_337_2706_3557);
        
        return tmp_2_339_2707_3559;
    } else {
        BoolTy fltIf_3228_3560 = i2_330_2700_3551 == n2_333_2703_3554;
        
        if (fltIf_3228_3560) {
            VectorTy *tmp_2_340_2708_3561 =
                      write_loop_seq_1260(j_331_2701_3552, i1_329_2699_3550, n1_332_2702_3553, src_1_335_2704_3555, tmp_337_2706_3557);
            
            return tmp_2_340_2708_3561;
        } else {
            FloatTy *tmp_24;
            
            tmp_24 = (FloatTy *) vector_nth(src_1_335_2704_3555,
                                            i1_329_2699_3550);
            
            FloatTy x1_341_2709_3564 = *tmp_24;
            FloatTy *tmp_23;
            
            tmp_23 = (FloatTy *) vector_nth(src_2_336_2705_3556,
                                            i2_330_2700_3551);
            
            FloatTy x2_342_2710_3567 = *tmp_23;
            BoolTy fltIf_3231_3570 = x1_341_2709_3564 < x2_342_2710_3567;
            IntTy fltPrm_3230_3572;
            
            if (fltIf_3231_3570) {
                IntTy flt_3798 = 0 - 1;
                
                fltPrm_3230_3572 = flt_3798;
            } else {
                BoolTy fltIf_3232_3571 = x1_341_2709_3564 > x2_342_2710_3567;
                
                if (fltIf_3232_3571) {
                    fltPrm_3230_3572 = 1;
                } else {
                    fltPrm_3230_3572 = 0;
                }
            }
            
            BoolTy fltIf_3229_3573 = fltPrm_3230_3572 < 0;
            
            if (fltIf_3229_3573) {
                VectorTy *tmp_1_343_2711_3577 =
                         vector_inplace_update(tmp_337_2706_3557,
                                               j_331_2701_3552,
                                               &x1_341_2709_3564);
                IntTy fltAppE_3233_3578 = i1_329_2699_3550 + 1;
                IntTy fltAppE_3234_3579 = j_331_2701_3552 + 1;
                VectorTy *tailapp_3777 =
                          writeMerge_seq_loop_1261_2178(fltAppE_3233_3578, i2_330_2700_3551, fltAppE_3234_3579, n1_332_2702_3553, n2_333_2703_3554, src_1_335_2704_3555, src_2_336_2705_3556, tmp_1_343_2711_3577);
                
                return tailapp_3777;
            } else {
                VectorTy *tmp_1_344_2712_3583 =
                         vector_inplace_update(tmp_337_2706_3557,
                                               j_331_2701_3552,
                                               &x2_342_2710_3567);
                IntTy fltAppE_3235_3584 = i2_330_2700_3551 + 1;
                IntTy fltAppE_3236_3585 = j_331_2701_3552 + 1;
                VectorTy *tailapp_3778 =
                          writeMerge_seq_loop_1261_2178(i1_329_2699_3550, fltAppE_3235_3584, fltAppE_3236_3585, n1_332_2702_3553, n2_333_2703_3554, src_1_335_2704_3555, src_2_336_2705_3556, tmp_1_344_2712_3583);
                
                return tailapp_3778;
            }
        }
    }
}
VectorTy *writeSort1_seq_1255_2189(VectorTy *src_270_2804_3591,
                                   VectorTy *tmp_271_2805_3592)
{
    IntTy len_273_2806_3594 = vector_length(src_270_2804_3591);
    BoolTy fltIf_3237_3595 = len_273_2806_3594 < 8192;
    
    if (fltIf_3237_3595) {
        VectorTy *tailprim_3779 = vector_inplace_sort(src_270_2804_3591,
                                                      compare_float);
        
        return tailprim_3779;
    } else {
        IntTy half_274_2807_3597 = len_273_2806_3594 / 2;
        IntTy len_406_2497_3114_3600 = vector_length(src_270_2804_3591);
        IntTy n__407_2498_3115_3601 =  maxInt(half_274_2807_3597, 0);
        IntTy m_408_2499_3116_3602 =
               minInt(n__407_2498_3115_3601, len_406_2497_3114_3600);
        IntTy fltAppE_3238_3603 = len_406_2497_3114_3600 -
              n__407_2498_3115_3601;
        IntTy m__409_2500_3117_3604 =  maxInt(0, fltAppE_3238_3603);
        VectorTy *fltPrd_3239_3605 = vector_slice(0, m_408_2499_3116_3602,
                                                  src_270_2804_3591);
        VectorTy *fltPrd_3240_3606 = vector_slice(m_408_2499_3116_3602,
                                                  m__409_2500_3117_3604,
                                                  src_270_2804_3591);
        IntTy len_406_2497_3120_3612 = vector_length(tmp_271_2805_3592);
        IntTy n__407_2498_3121_3613 =  maxInt(half_274_2807_3597, 0);
        IntTy m_408_2499_3122_3614 =
               minInt(n__407_2498_3121_3613, len_406_2497_3120_3612);
        IntTy fltAppE_3241_3615 = len_406_2497_3120_3612 -
              n__407_2498_3121_3613;
        IntTy m__409_2500_3123_3616 =  maxInt(0, fltAppE_3241_3615);
        VectorTy *fltPrd_3242_3617 = vector_slice(0, m_408_2499_3122_3614,
                                                  tmp_271_2805_3592);
        VectorTy *fltPrd_3243_3618 = vector_slice(m_408_2499_3122_3614,
                                                  m__409_2500_3123_3616,
                                                  tmp_271_2805_3592);
        VectorTy *tmp_l1_281_2814_3622 =
                  writeSort2_seq_1258_2190(fltPrd_3239_3605, fltPrd_3242_3617);
        VectorTy *tmp_r1_282_2815_3623 =
                  writeSort2_seq_1258_2190(fltPrd_3240_3606, fltPrd_3243_3618);
        IntTy n1_326_2696_3127_3627 = vector_length(tmp_l1_281_2814_3622);
        IntTy n2_327_2697_3128_3628 = vector_length(tmp_r1_282_2815_3623);
        VectorTy *res_328_2698_3129_3629 =
                  writeMerge_seq_loop_1261_2178(0, 0, 0, n1_326_2696_3127_3627, n2_327_2697_3128_3628, tmp_l1_281_2814_3622, tmp_r1_282_2815_3623, src_270_2804_3591);
        
        return res_328_2698_3129_3629;
    }
}
VectorTy *writeSort2_seq_1258_2190(VectorTy *src_237_2817_3631,
                                   VectorTy *tmp_238_2818_3632)
{
    IntTy len_240_2819_3634 = vector_length(src_237_2817_3631);
    BoolTy fltIf_3244_3635 = len_240_2819_3634 < 8192;
    
    if (fltIf_3244_3635) {
        VectorTy *tmp_1_241_2820_3636 =
                  write_loop_seq_1260(0, 0, len_240_2819_3634, src_237_2817_3631, tmp_238_2818_3632);
        VectorTy *tailprim_3780 = vector_inplace_sort(tmp_1_241_2820_3636,
                                                      compare_float);
        
        return tailprim_3780;
    } else {
        IntTy half_242_2821_3638 = len_240_2819_3634 / 2;
        IntTy len_406_2497_3134_3641 = vector_length(src_237_2817_3631);
        IntTy n__407_2498_3135_3642 =  maxInt(half_242_2821_3638, 0);
        IntTy m_408_2499_3136_3643 =
               minInt(n__407_2498_3135_3642, len_406_2497_3134_3641);
        IntTy fltAppE_3245_3644 = len_406_2497_3134_3641 -
              n__407_2498_3135_3642;
        IntTy m__409_2500_3137_3645 =  maxInt(0, fltAppE_3245_3644);
        VectorTy *fltPrd_3246_3646 = vector_slice(0, m_408_2499_3136_3643,
                                                  src_237_2817_3631);
        VectorTy *fltPrd_3247_3647 = vector_slice(m_408_2499_3136_3643,
                                                  m__409_2500_3137_3645,
                                                  src_237_2817_3631);
        IntTy len_406_2497_3140_3653 = vector_length(tmp_238_2818_3632);
        IntTy n__407_2498_3141_3654 =  maxInt(half_242_2821_3638, 0);
        IntTy m_408_2499_3142_3655 =
               minInt(n__407_2498_3141_3654, len_406_2497_3140_3653);
        IntTy fltAppE_3248_3656 = len_406_2497_3140_3653 -
              n__407_2498_3141_3654;
        IntTy m__409_2500_3143_3657 =  maxInt(0, fltAppE_3248_3656);
        VectorTy *fltPrd_3249_3658 = vector_slice(0, m_408_2499_3142_3655,
                                                  tmp_238_2818_3632);
        VectorTy *fltPrd_3250_3659 = vector_slice(m_408_2499_3142_3655,
                                                  m__409_2500_3143_3657,
                                                  tmp_238_2818_3632);
        VectorTy *src_l1_249_2828_3663 =
                  writeSort1_seq_1255_2189(fltPrd_3246_3646, fltPrd_3249_3658);
        VectorTy *src_r1_250_2829_3664 =
                  writeSort1_seq_1255_2189(fltPrd_3247_3647, fltPrd_3250_3659);
        IntTy n1_326_2696_3147_3668 = vector_length(src_l1_249_2828_3663);
        IntTy n2_327_2697_3148_3669 = vector_length(src_r1_250_2829_3664);
        VectorTy *res_328_2698_3149_3670 =
                  writeMerge_seq_loop_1261_2178(0, 0, 0, n1_326_2696_3147_3668, n2_327_2697_3148_3669, src_l1_249_2828_3663, src_r1_250_2829_3664, tmp_238_2818_3632);
        
        return res_328_2698_3149_3670;
    }
}
unsigned char check_sorted_1227_2143(VectorTy *sorted_207_2839_3672)
{
    IntTy len_209_2840_3674 = vector_length(sorted_207_2839_3672);
    BoolTy fltIf_3251_3675 = len_209_2840_3674 <= 1;
    
    if (fltIf_3251_3675) {
        unsigned char tailapp_3781 =  print_check(true);
        
        return tailapp_3781;
    } else {
        IntTy n_397_2517_3156_3678 = len_209_2840_3674 - 2;
        VectorTy *arr1_210_2841_3680 = vector_slice(0, n_397_2517_3156_3678,
                                                    sorted_207_2839_3672);
        IntTy fltAppE_3253_3684 = vector_length(arr1_210_2841_3680);
        BoolTy check_215_2842_3685 =
                ifoldl_loop_1249_2193(0, fltAppE_3253_3684, true, arr1_210_2841_3680, arr1_210_2841_3680);
        unsigned char tailapp_3782 =  print_check(check_215_2842_3685);
        
        return tailapp_3782;
    }
}
BoolTy ifoldl_loop_1249_2193(IntTy idx_503_2843_3686, IntTy end_504_2844_3687,
                             BoolTy acc_506_2845_3688,
                             VectorTy *vec_507_2846_3689,
                             VectorTy *arr1_210_2847_3690)
{
    BoolTy fltIf_3254_3691 = idx_503_2843_3686 == end_504_2844_3687;
    
    if (fltIf_3254_3691) {
        return acc_506_2845_3688;
    } else {
        FloatTy *tmp_26;
        
        tmp_26 = (FloatTy *) vector_nth(vec_507_2846_3689, idx_503_2843_3686);
        
        FloatTy elt1_211_2833_3163_3694 = *tmp_26;
        IntTy fltAppE_3255_3696 = idx_503_2843_3686 + 1;
        FloatTy *tmp_25;
        
        tmp_25 = (FloatTy *) vector_nth(arr1_210_2847_3690, fltAppE_3255_3696);
        
        FloatTy elt2_214_2835_3165_3697 = *tmp_25;
        BoolTy fltIf_3167_3285_3746 = elt1_211_2833_3163_3694 <
               elt2_214_2835_3165_3697;
        IntTy fltPrm_3257_3698;
        
        if (fltIf_3167_3285_3746) {
            IntTy flt_3807 = 0 - 1;
            
            fltPrm_3257_3698 = flt_3807;
        } else {
            BoolTy fltIf_3168_3286_3747 = elt1_211_2833_3163_3694 >
                   elt2_214_2835_3165_3697;
            
            if (fltIf_3168_3286_3747) {
                fltPrm_3257_3698 = 1;
            } else {
                fltPrm_3257_3698 = 0;
            }
        }
        
        BoolTy fltPrm_3256_3699 = fltPrm_3257_3698 <= 0;
        BoolTy acc1_510_2848_3700 = acc_506_2845_3688 && fltPrm_3256_3699;
        IntTy fltAppE_3258_3701 = idx_503_2843_3686 + 1;
        BoolTy tailapp_3783 =
                ifoldl_loop_1249_2193(fltAppE_3258_3701, end_504_2844_3687, acc1_510_2848_3700, vec_507_2846_3689, arr1_210_2847_3690);
        
        return tailapp_3783;
    }
}
int __main_expr()
{
    add_symbol(3787, "OK\n");
    add_symbol(3788, "Err\n");
    
    unsigned char tailapp_3784 =  bench_main();
    
    printf("'#()");
    printf("\n");
    free_symtable();
    return 0;
}