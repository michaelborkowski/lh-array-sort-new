# lh-array-sort
Various "in place" sorting algorithms verified with LH

Now have: Proof of Sortedness for Merge, Linear Merge and Insertion, Proof of Equivalence for all using Bag

Array are implemented using { List, left: Int, right: Int } with slice api

Checking time should not exceed 2min for any single file. Slightly faster than List implementation of Array (main branch)


## Cabal-based building and benchmarking


### Building


- Pure list backend:

  - Liquid checks but no linear checks:

    ```shellsession
      cabal build lh-array-sort
    ```

  - Linear checks but no liquid checks:

    ```shellsession
      cabal build lh-array-sort -f-liquid-checks
    ```

- Mutable arrays backend, no checks:

    ```shellsession
     cabal build lh-array-sort -fmutable-arrays
    ```
     
### Benchmarking

The `benchrunner` package in the repository provides an executable to run benchmarks.
But

First, you need to make sure that you compiled the mutable-arrays backend. 
You can either add `--constraint="lh-array-sort +mutable-arrays"` to every call
to `cabal run` below (add it right after "run") or call

``` shellsession
cabal configure --constraint="lh-array-sort +mutable-arrays"
```

once before benchmarking. This command will create a `cabal.project.local` file
asserting the mutable-arrays constraint. Note that this constraint will be in
action until you remove the file.


The interface for `benchrunner` is:

```shellsession
benchrunner ITERS SORT PAR SIZE
```

For instance:

```shellsession
cabal run benchrunner -- 5 Mergesort Seq 10000
cabal run benchrunner -- 5 Mergesort Par 10000 +RTS -N4
cabal run benchrunner -- 5 Insertionsort Seq 10000
```


## Make-based building and benchmarking (somewhat outdated in February 2025)

Note: for an explanation of how building with LiquidHaskell v. Linear-Haskell checks works, see
https://github.com/michaelborkowski/lh-array-sort/pull/5


This project is set up to be built using `make`. By default all make
commands will use Cabal to build Haskell stuff and will compile verified
algorithms using list-based arrays. Both of these defaults can be changed using
command-line flags; use `STACK=1` to build using Stack and `MUTABLE_ARRAYS=1`
to compile with mutable arrays. For example, `make all STACK=1 MUTABLE_ARRAYS=1`
will build using Stack and mutable arrays.


The following make commands are available:

- A one-liner to build everything and run all benchmarks:
    `make all`

- To build everything:
    `make build`

- To run all benchmarks:
    `make bench`

- Print version numbers of various compilers and build tools:
    `make checkdeps`

  N.B. The name is a bit misleading. This doesn't actually check if the version
  numbers match some expected number. That's because all of us might not be using
  the exact same tools, except maybe GHC-8.10.7. But once we get there we can
  change the behavior of this command.

- Delete build artifacts (just cleans up the C stuff but not Cabal/Stack):
    `make clean`

- Some more fine grained commands:

  - Run verified versions of benchmarks:
      `make bench_verified`

  - Run canonical C versions of benchmarks (glibc insertion sort etc.):
      `make bench_canonical_c`

  - Run Gibbon versions of benchmarks:
      `make bench_gibbon_c`

  - Build all Haskell code:
      `make build_haskell`

  - Build all C code:
       `make build_c`
