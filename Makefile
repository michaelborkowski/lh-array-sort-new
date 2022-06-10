HC = ghc
CC = gcc

# Flag to decide whether we're using stack or cabal.
ifeq ($(STACK),1)
	STK = stack
	HCTOOL = stack
	HCTOOLEXEC = exec
else
	CABAL = cabal
	HCTOOL = cabal
	HCTOOLEXEC = v2-exec
endif


# Flag to decide whether we're using mutable arrays.
ifeq ($(MUTABLE_ARRAYS),1)
	F_MUTABLE_ARRAYS = -fmutable-arrays
else
	F_MUTABLE_ARRAYS = -fno-mutable-arrays
endif

all: checkdeps build bench

bench: bench_verified bench_canonical_c bench_gibbon_c

bench_verified:
	$(HCTOOL) $(HCTOOLEXEC) $(F_MUTABLE_ARRAYS) benchrunner -- FillArray 1000000
	$(HCTOOL) $(HCTOOLEXEC) $(F_MUTABLE_ARRAYS) benchrunner -- Insertionsort 10
	$(HCTOOL) $(HCTOOLEXEC) $(F_MUTABLE_ARRAYS) benchrunner -- Insertionsort 100
	$(HCTOOL) $(HCTOOLEXEC) $(F_MUTABLE_ARRAYS) benchrunner -- Insertionsort 1000

bench_gibbon_c:
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive ./benchmarks/c/cbench.exe gib_fillarray int64 1000000
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive ./benchmarks/c/cbench.exe gib_insertionsort2 int64 10
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive ./benchmarks/c/cbench.exe gib_insertionsort2 int64 100
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive ./benchmarks/c/cbench.exe gib_insertionsort2 int64 1000

bench_canonical_c:
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive ./benchmarks/c/cbench.exe fillarray int64 1000000
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive ./benchmarks/c/cbench.exe insertionsort int64 10
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive ./benchmarks/c/cbench.exe insertionsort int64 100
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive ./benchmarks/c/cbench.exe insertionsort int64 1000

build: build_haskell build_c

build_haskell:
ifeq ($(STACK),1)
# CSK: verify that this does indeed build everything, including criterion-external.
	$(STK) build $(F_MUTABLE_ARRAYS)
	$(STK) build criterion-external
else
	$(CABAL) v2-build all $(F_MUTABLE_ARRAYS)
	$(CABAL) v2-build criterion-external
endif


build_c:
	@cd benchmarks/c && make

checkdeps:
	@echo -e "Using" $(HCTOOL) "to build Haskell stuff.\n"
	$(HCTOOL) --version
	$(CC) --version
	$(HC) --version


clean:
	cd benchmarks/c && make clean

.PHONY: all build build_haskell build_c bench bench_verified bench_gibbon_c bench_canonical_c clean
