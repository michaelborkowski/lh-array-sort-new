#pragma once

#include "benchmarks.h"
#include <algorithm> // For std::min and std::copy
// referenced from here: https://en.wikipedia.org/wiki/Merge_sort

template <typename T>
void bottomUpMerge(T *a, size_t left, size_t right, size_t end, T *b){
    size_t i = left;
    size_t j = right;

    for (size_t k = left; k < end; k++){
        if (i < right && (j >= end || a[i] <= a[j])){
            b[k] = a[i];
            i++;
        }
        else{
            b[k] = a[j];
            j++;
        }
    }
}

template <typename T>
inline T *bottomUpMergeSort(T *a, T *b, size_t n){

    for (size_t width = 1; width < n; width = 2 * width){
        for (size_t i = 0; i < n; i = i + 2 * width){
            bottomUpMerge(a, i, std::min(i + width, n), std::min(i + 2 * width, n), b);
        }
        std::copy(b, b + n, a);
    }

    return a;
}