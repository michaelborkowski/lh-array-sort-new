#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include "benchmarks.h"
#include "helpers.h"

// Switch from parallel to sequential sort.
#define SEQCUTOFF 4096

// Switch to insertion sort.
#define INSERTIONSIZE 8192

// -----------------------------------------------------------------------------

// Sequential.
void writesort1(slice_t src, slice_t tmp);
void writesort2(slice_t src, slice_t tmp);
void merge(slice_t left, slice_t right, slice_t dst);
