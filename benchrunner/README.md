A Haskell script to run all benchmarks. Although it can only run
lh-array-sort versions (and not C, Gibbon etc.) at the moment.


To run, use one of the following commands:

    $ cabal v2-exec benchrunner -fno-mutable-arrays -- ITERS Insertionsort ParOrSeq NUM_ELTS
    
or

    $ cabal v2-exec benchrunner -fmutable-arrays -- ITERS Mergesort ParOrSeq NUM_ELTS
    
or

    $ cabal v2-exec benchrunner -fmutable-arrays -- ITERS FillArray ParOrSeq NUM_ELTS

To run the sorting algorithms from vector-algorithms, use the following commands: 

    $ cabal run benchrunner -- ITERS "VectorSort Insertionsort" ParOrSeq NUM_ELTS
    $ cabal run benchrunner -- ITERS "VectorSort Mergesort" ParOrSeq NUM_ELTS
    $ cabal run benchrunner -- ITERS "VectorSort Quicksort" ParOrSeq NUM_ELTS