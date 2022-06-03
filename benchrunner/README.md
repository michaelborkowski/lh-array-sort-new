A Haskell script to run all benchmarks. Although it can only run
lh-array-sort versions (and not C, Gibbon etc.) at the moment.


To run, use one of the following commands:

    $ cabal v2-exec benchrunner -fno-mutable-arrays -- Insertionsort NUM_ELTS
    
or

    $ cabal v2-exec benchrunner -fmutable-arrays -- Mergesort NUM_ELTS
    
or

    $ cabal v2-exec benchrunner -fmutable-arrays -- FillArray NUM_ELTS
