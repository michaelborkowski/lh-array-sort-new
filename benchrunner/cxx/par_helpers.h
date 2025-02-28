#ifdef CILK
#include "helpers.h"
#include <cilk/cilk.h>

void our_memcpy_par(void *dst, void *src, size_t nbytes);

static inline void slice_copy_par(slice_t *src, slice_t *dst)
{
    our_memcpy_par(dst->base, src->base, (src->total_elems * src->elt_size));
    return;
}
#endif
