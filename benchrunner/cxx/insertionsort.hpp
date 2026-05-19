#pragma once

#include "benchmarks.h"
#include <utility>

template<typename T>
inline T *insertionsort_inplace(T *pbase, size_t total_elems)
{
    if (total_elems <= 1) return pbase;

    for (size_t i = 1; i < total_elems; ++i) {
        T key = std::move(pbase[i]);
        size_t j = i;
        while (j > 0 && pbase[j - 1] > key) {
            pbase[j] = std::move(pbase[j - 1]);
            --j;
        }
        pbase[j] = std::move(key);
    }

    return pbase;
}