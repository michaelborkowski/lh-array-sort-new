## Testing Methodology

### Setup
To install the testing software, run:
```
sudo apt install hyperfine cloc
```

### Verification Time
To test the verification time, cd into the directory of the sort you want to test (e.g., `cd statistic-calculations/insertionsort`), then run:
```
hyperfine \
--warmup 1 \
--runs 10 \
'cabal clean && cabal build'
```

Since this does a completely new build, to find the verification time of specific sorting algorithms, subtract the average time to build `common-lemmas` from the average time to build the sort.

Note: we chose to use build time as a proxy for verification time for simplicity. A command like:
```
hyperfine \
--warmup 1 \
--runs 10 \
'rm -rf .liquid && liquid src/Insertion.hs' 
```
might be a more exact representation of verification time alone.

### Lines of code/proofs
To find the lines of code, cd into the directory of the sort you want to test (e.g., `cd statistic-calculations/insertionsort`), then run `cloc src`. From there, manually count and subtract the number of proof lines from the `code` column.

Note: some lines count as both proof and code, namely, lines with `?` annotations.

## Configuration

### Flags
 - `mutable-arrays`: `False` \
 - `prim-mutable-arrays`: `False` \
 - `liquid-checks`: `True` \
 - `runtime-checks`: `False`

### Software Versions
 - GHC: `9.10.3` \
 - Z3: `4.8.12` - 64 bit \
 - CPU: AMD Ryzen 7 7730U \
 - RAM: 32GB
