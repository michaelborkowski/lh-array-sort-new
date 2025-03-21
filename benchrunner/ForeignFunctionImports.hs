module ForeignFunctionImports (c_insertionsort, c_mergesort, c_quicksort, cxx_int_insertionsort, cxx_int_mergesort, cxx_int_quicksort, SortFn, SortFnCxx) where

import Foreign as F
import Foreign.C.Types as CTypes

-- Import C sorts functions from ./csorts

type SortFn = Ptr Int64 -> CTypes.CSize -> CTypes.CSize -> IO (Ptr Int64)
foreign import ccall "insertionsort_inplace" c_insertionsort :: SortFn
foreign import ccall "smergesort" c_mergesort :: SortFn
foreign import ccall "quicksort_inplace" c_quicksort :: SortFn

type SortFnCxx = Ptr Int64 -> CTypes.CSize -> IO (Ptr Int64)
foreign import ccall "insertionsort_cxx_int" cxx_int_insertionsort :: SortFnCxx
foreign import ccall "bottom_up_merge_sort_cxx_int" cxx_int_mergesort :: SortFnCxx
foreign import ccall "quicksort_cxx_int" cxx_int_quicksort :: SortFnCxx
