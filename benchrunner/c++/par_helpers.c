#ifdef CILK
#include "par_helpers.h"

void our_memcpy_par(void *dst, void *src, size_t nbytes)
{
    if (nbytes <= 8192) {
        our_memcpy(dst, src, nbytes);
        return;
    }
    size_t half = nbytes / 2;

    cilk_spawn our_memcpy_par(dst, src, half);
    our_memcpy_par((char*)dst + half, (char*)src + half, nbytes - half);
    cilk_sync;

    return;
}
#endif
