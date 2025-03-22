#include "benchmarks.h"

// -----------------------------------------------------------------------------
//     i ← 1
//     while i < n
//         temp ← array[i]
//         j ← i
//         while j > 0 and array[j - 1] > temp
//             array[j] ← array[j - 1]
//             j ← j - 1
//         end while
//         array[j] ← temp
//         i ← i + 1
//     end while

template<typename T>
T *insertionsort_inplace(T *pbase, size_t total_elems)
{
    int i = 0;
    while (i < total_elems){
        T temp = pbase[i];
        int j = i;
        while(j > 0 && pbase[j - 1] > temp){
            pbase[j] = pbase[j-1];
            j = j - 1;
        }
        pbase[j] = temp;
        i = i + 1;
    }

    return pbase;
}
