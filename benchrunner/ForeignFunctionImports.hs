module ForeignFunctionImports (c_insertionsort, c_mergesort, c_quicksort, SortFn) where
    
import Foreign as F
import Foreign.C.Types as CTypes

-- Import C sorts functions from ./csorts 

type SortFn = Ptr Int64 -> CTypes.CSize -> CTypes.CSize -> IO (Ptr Int64)
foreign import ccall "insertionsort_inplace" c_insertionsort :: SortFn
foreign import ccall "smergesort" c_mergesort :: SortFn
foreign import ccall "quicksort" c_quicksort :: SortFn
