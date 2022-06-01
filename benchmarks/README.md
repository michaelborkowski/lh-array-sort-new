A place to store all benchmark programs.


You can run the C benchmarks as following:

(1) `cd ./c/ && make`
(2) `./criterion-interactive ./c/cbench.exe fillarray int64 1000000` or
    `./criterion-interactive ./c/cbench.exe insertionsort int64 1000000`


These commands depend on the `criterion-interactive` executable, but this isn't part of the automated build yet. TODO: fix this. For now, you can build this package separately and use it here.
