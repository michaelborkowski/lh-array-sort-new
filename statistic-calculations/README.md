## Testing Methodology

### Setup
To install the testing software, run:
```
sudo apt install hyperfine
```
<!-- ```
sudo apt install hyperfine cloc
``` -->

### Verification Time
To test the verification time, cd into the directory of the sort you want to test (e.g., `cd statistic-calculations/insertionsort`), then run:
```
hyperfine \
--warmup 1 \
--runs 3 \
'cabal clean && cabal build'
```
<!--
Note: you might be able to use `cabal install --lib --package-env ~/temp_global_buf common-lemmas`
to circumvent rebuilding the common lemmas every build (don't forget to remove common-lemmas from the project file while doing so) -->

Since this does a completely new build, to find the verification time of specific sorting algorithms, subtract the average time to build `common-lemmas` from the average time to build the sort. Repeat this to get the build + verification time of each individual sort.

From there, you can use the same process with
```
hyperfine \
--warmup 1 \
--runs 3 \
'cabal clean && cabal build --flags="-liquid-checks"'
```
to get the build time of each sort. Subtract the build time from the build + verification time to isolate the verification time for each sorting algorithm. Essentially, the equation for verification time is: \
`average build_plus_verification time of sort - average build_plus_verification time of common lemmas - (average build time of sort - average build time of common lemmas)`.

<!-- Note: A command like:
```
hyperfine \
--warmup 1 \
--runs 3 \
'rm -rf .liquid && liquid src/Insertion.hs' 
```
might be a more exact representation of verification time alone. -->

### Lines of implementation/proofs
We count the lines of implementation/proofs manually. To simplify this process, we separated lemmas and implementation with clear comments where possible. When counting, you may find it helpful to temporarily delete all non-implementation or non-proof lines rather than counting each one in the original file.

When counting implementation lines, we did not include defines, #ifdefs, includes, and other build-related lines of code.
<!-- To find the lines of code, cd into the directory of the sort you want to test (e.g., `cd statistic-calculations/insertionsort`), then run `cloc src`. From there, manually count and subtract the number of proof lines and the number of comments from the sum of the `comments` and `code` columns (some proof lines are counted as comments).

Note: some lines count as both proof and code, namely, lines with `?` annotations. Even if a function is reflected, we consider its body to be code lines not proof lines. -->

## Configuration

### Flags
 - `mutable-arrays`: `False`
 - `prim-mutable-arrays`: `False`
 - `liquid-checks`: `True`
 - `runtime-checks`: `False`

### Software Versions
 - GHC: `9.10.3`
 - Z3: `4.8.12` - 64 bit
 - CPU: AMD Ryzen 7 7730U
 - RAM: 32GB
