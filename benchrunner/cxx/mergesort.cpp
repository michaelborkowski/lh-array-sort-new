#include "benchmarks.h"
// referenced from here: https://en.wikipedia.org/wiki/Merge_sort

template <typename T>
T *bottomUpMergeSort(T *a, T *b, int n){

    for (int width = 1; width < n; width = 2 * width){

        for (int i = 0; i < n; i = i + 2 * width){
            bottomUpMerge(a, i, std::min(i + width, n), std::min(i + 2 * width, n), b);
        }
        copyArray(b, a, n);
    }

    return a;
}

template <typename T>
void bottomUpMerge(T *a, int left, int right, int end, T *b){

    int i = left;
    int j = right;

    for (int k = left; k < end; k++){
        if (i < right && (j >= end || a[i] <= a[j])){
            b[k] = a[i];
            i = i + 1;
        }
        else{
            b[k] = a[j];
            j = j + 1;
        }
    }
}

template <typename T>
void copyArray(T *b, T* a, int n){
    int i;
    for (i = 0; i < n; i++){
        a[i] = b[i];
    }
}
