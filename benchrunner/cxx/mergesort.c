#include "mergesort_common.h"

// -----------------------------------------------------------------------------

// // Whether this mergesort should actually be cilksort.
// static bool CILKSORT = false;

// // Sequential cilksort.
// void *cilksort(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp)
// {
//     CILKSORT = true;
//     void *sorted = smergesort_cmp(pbase, total_elems, size, cmp);
//     CILKSORT = false;
//     return sorted;
// }

// // Sequential mergesort.
// void *smergesort(void *const pbase, size_t total_elems, size_t size)
// {
//     // Copy into a fresh array.
//     char *cpy = (char *) malloc(total_elems * size);
//     if (cpy == NULL) {
//         fprintf(stderr, "mergesort: couldn't allocate");
//         exit(1);
//     }
//     our_memcpy(cpy, (char *) pbase, (size * total_elems));

//     // Temporary buffer.
//     char *tmp = (char *) malloc(total_elems * size);
//     if (tmp == NULL) {
//         fprintf(stderr, "mergesort: couldn't allocate");
//         exit(1);
//     }

//     slice_t cpy_sl = (slice_t) {cpy, total_elems, size};
//     slice_t tmp_sl = (slice_t) {tmp, total_elems, size};

//     writesort1(cpy_sl, tmp_sl, compare_int64s);

//     return cpy;
// }

// // Sequential mergesort.
// void *smergesort_cmp(void *const pbase, size_t total_elems, size_t size, __compar_fn_t cmp)
// {
//     // Copy into a fresh array.
//     char *cpy = (char *) malloc(total_elems * size);
//     if (cpy == NULL) {
//         fprintf(stderr, "mergesort: couldn't allocate");
//         exit(1);
//     }
//     our_memcpy(cpy, (char *) pbase, (size * total_elems));

//     // Temporary buffer.
//     char *tmp = (char *) malloc(total_elems * size);
//     if (tmp == NULL) {
//         fprintf(stderr, "mergesort: couldn't allocate");
//         exit(1);
//     }

//     slice_t cpy_sl = (slice_t) {cpy, total_elems, size};
//     slice_t tmp_sl = (slice_t) {tmp, total_elems, size};

//     writesort1(cpy_sl, tmp_sl, cmp);

//     return cpy;
// }

// // -----------------------------------------------------------------------------

// // Uses "tmp" to sort "src" in place.
// void writesort1(slice_t src, slice_t tmp, __compar_fn_t cmp)
// {
//     size_t len = slice_length(&src);
//     if (CILKSORT && (len < INSERTIONSIZE)) {
//         // insertionsort_inplace(src.base, src.total_elems, src.elt_size, CMP);
//         qsort(src.base, src.total_elems, src.elt_size, cmp);
//         // quicksort_inplace(src.base, src.total_elems, src.elt_size, CMP);
//         return;
//     }
//     if (len == 1) {
//         return;
//     }
//     size_t half = len / 2;
//     slice_prod_t splitsrc = slice_split_at(&src, half);
//     slice_prod_t splittmp = slice_split_at(&tmp, half);
//     writesort2(splitsrc.left, splittmp.left, cmp);
//     writesort2(splitsrc.right, splittmp.right, cmp);
//     merge(splittmp.left, splittmp.right, src, cmp);
//     return;
// }

// // Uses "src" to sort "tmp" in place.
// void writesort2(slice_t src, slice_t tmp, __compar_fn_t cmp)
// {
//     size_t len = slice_length(&src);
//     if (CILKSORT && (len < INSERTIONSIZE)) {
//         slice_copy(&src, &tmp);
//         // insertionsort_inplace(tmp.base, tmp.total_elems, tmp.elt_size, CMP);
//         qsort(tmp.base, tmp.total_elems, tmp.elt_size, cmp);
//         // quicksort_inplace(tmp.base, tmp.total_elems, tmp.elt_size, CMP);
//         return;
//     }
//     if (len == 1) {
//         slice_copy(&src, &tmp);
//         return;
//     }
//     size_t half = len / 2;
//     slice_prod_t splitsrc = slice_split_at(&src, half);
//     slice_prod_t splittmp = slice_split_at(&tmp, half);
//     writesort1(splitsrc.left, splittmp.left, cmp);
//     writesort1(splitsrc.right, splittmp.right, cmp);
//     merge(splitsrc.left, splitsrc.right, tmp, cmp);
//     return;
// }

// size_t binary_search(slice_t *sl, void *query, __compar_fn_t cmp)
// {
//     size_t lo = 0;
//     size_t hi = slice_length(sl);

//     size_t n, mid;
//     void *pivot;
//     int tst;

//     while (hi > lo) {
//         n = hi - lo;
//         mid = lo + (n/2);
//         pivot = slice_nth(sl, mid);
//         tst = (*cmp)(query, pivot);
//         if (tst == 0) {
//             return mid;
//         }
//         if (tst < 0) {
//             hi = mid;
//         } else {
//             lo = mid+1;
//         }
//     }

//     return lo;
// }

// void merge(slice_t left, slice_t right, slice_t dst,  __compar_fn_t cmp)
// {
//     size_t i=0, j=0, k=0;
//     size_t n1 = slice_length(&left);
//     size_t n2 = slice_length(&right);

//     void *elt_l, *elt_r;

//     while (i < n1 && j < n2) {
//         elt_l = slice_nth(&left, i);
//         elt_r = slice_nth(&right, j);
//         if ((*cmp)(elt_l, elt_r) <= 0) {
//             slice_inplace_update(&dst, k, elt_l);
//             i++;
//         } else {
//             slice_inplace_update(&dst, k, elt_r);
//             j++;
//         }
//         k++;
//     }

//     // Use slice_copy.
//     while (i < n1) {
//         elt_l = slice_nth(&left, i);
//         slice_inplace_update(&dst, k, elt_l);
//         i++;
//         k++;
//     }

//     // Use slice_copy.
//     while (j < n2) {
//         elt_r = slice_nth(&right, j);
//         slice_inplace_update(&dst, k, elt_r);
//         j++;
//         k++;
//     }

//     return;
// }


// referenced from here: https://en.wikipedia.org/wiki/Merge_sort


template <typename T>
void bottomUpMergeSort(T *a, T *b, int n){

    for (int width = 1; width < n; width = 2 * width){

        for (int i = 0; i < n; i = i + 2 * width){
            bottomUpMerge(a, i, std::min(i + width, n), std::min(i + 2 * width, n), b);
        }
        copyArray(b, a, n);
    }
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
