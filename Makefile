HC = ghc
CC = gcc
RTFLAGS = +RTS -N6
CSORTS_DIR = $(PWD)/benchrunner/csorts/
CSORTS_EXEC = cbench.exe
CSORTS_EXEC_FULL := $(CSORTS_DIR)$(CSORTS_EXEC) 

# Flag to decide whether we're using stack or cabal.
ifeq ($(STACK),1)
	STK = stack
	HCTOOL = stack
	HCTOOLEXEC = exec
ifeq ($(MUTABLE_ARRAYS),1)
		F_MUTABLE_ARRAYS = --flag lh-array-sort:mutable-arrays
else
		F_MUTABLE_ARRAYS = --flag lh-array-sort:-mutable-arrays
endif
else
	CABAL = cabal-3.12.1.0
	HCTOOL = cabal-3.12.1.0 
	HCTOOLEXEC = v2-exec
ifeq ($(MUTABLE_ARRAYS),1)
		F_MUTABLE_ARRAYS = -fmutable-arrays
else
		F_MUTABLE_ARRAYS = -fno-mutable-arrays
endif
endif

all: checkdeps build bench

bench: bench_verified bench_canonical_c bench_gibbon_c

bench_verified:
	#$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- FillArray 10000000      {-Errors out-}
	$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- 1 Insertionsort Seq 10
	$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- 1 Insertionsort Seq 100
	$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- 1 Insertionsort Seq 1000
	$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- 1 Mergesort Seq 20
	$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- 1 Mergesort Seq 100
	$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- 1 Mergesort Seq 10000
	$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- 1 Mergesort Seq 100000
	$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- 1 Mergesort Seq 1000000
	$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- 1 Mergesort Seq 4000000
#	$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- Quicksort 1000
#	$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- Quicksort 10000
#	$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- Quicksort 100000
	$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- 1 Cilksort Seq 1000
	$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- 1 Cilksort Seq 10000
	$(HCTOOL) $(HCTOOLEXEC)  benchrunner $(RTFLAGS) -- 1 Cilksort Seq 100000

bench_gibbon_c:
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive $(CSORTS_EXEC_FULL) gib_fillarray int64 10000000
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive $(CSORTS_EXEC_FULL) gib_insertionsort2 int64 10
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive $(CSORTS_EXEC_FULL) gib_insertionsort2 int64 100
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive $(CSORTS_EXEC_FULL) gib_insertionsort2 int64 1000

bench_canonical_c:
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive $(CSORTS_EXEC_FULL) fillarray int64 10000000
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive $(CSORTS_EXEC_FULL) sumarray int64 10000000
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive $(CSORTS_EXEC_FULL) insertionsort int64 10
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive $(CSORTS_EXEC_FULL) insertionsort int64 100
	$(HCTOOL) $(HCTOOLEXEC) criterion-interactive $(CSORTS_EXEC_FULL) insertionsort int64 1000

build: build_haskell build_c

build_haskell:
ifeq ($(STACK),1)
# CSK: verify that this does indeed build everything, including criterion-external.
	$(STK) build $(F_MUTABLE_ARRAYS)
	$(STK) build criterion-external
else    
	#$(CABAL) configure --enable-library-profiling --enable-profiling
	$(CABAL) v2-build all $(F_MUTABLE_ARRAYS)
	$(CABAL) v2-build criterion-external
endif


build_c:
	@cd $(CSORTS_DIR) && make
	cabal v2-build criterion-interactive

checkdeps:
	@echo -e "Using" $(HCTOOL) "to build Haskell stuff.\n"
	$(HCTOOL) --version
	$(CC) --version
	$(HC) --version


clean:
	cd $(CSORTS_DIR) && make clean

.PHONY: all build build_haskell build_c bench bench_verified bench_gibbon_c bench_canonical_c clean
