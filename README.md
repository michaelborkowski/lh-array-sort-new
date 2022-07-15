# lh-array-sort
Various "in place" sorting algorithms verified with LH

Now have: Proof of Sortedness for Merge, Linear Merge and Insertion, Proof of Equivalence for all using Bag

Array are implemented using { List, left: Int, right: Int } with slice api

Checking time should not exceed 2min for any single file. Slightly faster than List implementation of Array (main branch)


## Building and benchmarking


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
