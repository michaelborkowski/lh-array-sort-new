## Purpose

This directory contains a Python re-implementation of the Haskell Criterion methodology to run executables (instead of Haskell functions, like Criterion normally does).
One could call it "benchrunner-runner" because the purpose is to run `benchrunner` many times and calculate the appropriate run time statistics.

We take as input some program `prog` with the following interface:

- `prog` takes `iters` as a command-line argument,
- `prog` measures run time of a function of interest in a tight loop that repeats `iters` many times, and finally
- `prog` prints to stdout the batchtime (total loop time) and selftimed (total loop time divided by `iters`).

The ultimate goal is then to sweep `iters` and perform a linear regression against `iters` and `batchtime`.
The slope is the mean and the y-intercept represents some notion of shared overhead, insensitive to `iters`.

## Run

This package contains two scripts:

- `sweep_seq.py` (top level)
- `criterionmethodology.py` (called by `sweep_seq.py`)

Both can be ran directly, i.e.:

```shellsession
criterionmethodology benchrunner Quicksort Seq 2000
```

will call `benchrunner iters Quicksort Seq 2000` for various `iters`.

`sweep_seq` performs a logarithmic sweep over different array sizes, invoking `criterionmethdology.py` at each point.

## Arightmetic vs geometric mean

Since performance data is non-negative and judged multiplicatively (twice as good means numbers are half, twice has bad means numbers are doubled; these are all *factors*), the geomean and geo-standard-deviation may make more sense theoretically.
However, from some testing, the geomean seems to vary wildly for programs with fleeting execution times, even between repeated runs with the same parameters.

In particular, to compute the geomean, we:

- take the logarithm of all the `x` and `y` values,
- compute linear regression over that, then 
- exponentiate the y-intercept.

The other dependent portion, which is the slope, becomes a power (the equation is `y = e^b x^m`), which represents *geometric overhead*, e.g. how much overhead is being added per iteration.
This may do well to model any slowdowns, e.g. ones arising from pre-allocating arrays.
