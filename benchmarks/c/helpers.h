#ifndef _HELPERS_H
#define _HELPERS_H

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <errno.h>
#include <time.h>

// -----------------------------------------------------------------------------

static inline double difftimespecs(struct timespec* t0, struct timespec* t1)
{
    return (double)(t1->tv_sec - t0->tv_sec)
            + ((double)(t1->tv_nsec - t0->tv_nsec) / 1000000000.0);
}

static inline int compare_int64s(const void* a, const void* b)
{
    int64_t arg1 = *(const int64_t*)a;
    int64_t arg2 = *(const int64_t*)b;

    if (arg1 < arg2) return -1;
    if (arg1 > arg2) return 1;
    return 0;
}

static inline bool prefix(const char *pre, const char *str)
{
    return strncmp(pre, str, strlen(pre)) == 0;
}

static inline void our_memcpy(void *dst, void *src, size_t nbytes)
{
    memcpy(dst, src, nbytes);
}

// Sequential for now.
static inline void our_memcpy_par(void *dst, void *src, size_t nbytes)
{
    memcpy(dst, src, nbytes);
}

typedef struct slice_t_ {
    void *base;
    size_t total_elems;
    size_t elt_size;
} slice_t;

typedef struct slice_prod_t_ {
    slice_t left;
    slice_t right;
} slice_prod_t;

static inline size_t slice_length(const slice_t *sl)
{
    return sl->total_elems;
}

static inline void *slice_nth(const slice_t *sl, size_t n)
{
    return (char*) sl->base + (n * sl->elt_size);
}

static inline void slice_copy(slice_t *src, slice_t *dst)
{
    our_memcpy(dst->base, src->base, (src->total_elems * src->elt_size));
    return;
}

static inline void slice_inplace_update(slice_t *sl, size_t i, void* elt) {
    void* dst = slice_nth(sl, i);
    our_memcpy(dst, elt, sl->elt_size);
}

static inline slice_prod_t slice_split_at(const slice_t *sl, size_t idx)
{
    slice_t left = (slice_t) { sl->base, idx, sl->elt_size };
    slice_t right = (slice_t) { (char*) sl->base + (sl->elt_size * idx),
                                (sl->total_elems - idx),
                                sl->elt_size };
    return (slice_prod_t) { left, right };
}

static inline void slice_print(const slice_t *sl)
{
    printf("[");
    char *elt;
    for (size_t i = 0; i < sl->total_elems; i++) {
        elt = (char*) sl->base + (i * sl->elt_size);
        if (sl->elt_size == sizeof(int64_t)) {
            printf("%ld, ", *(int64_t*) elt);
        } else {
            printf("%p, ", elt);
        }
    }
    printf("]\n");
}

#endif
