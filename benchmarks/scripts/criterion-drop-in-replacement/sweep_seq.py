#!/usr/bin/env python3
import os
import numpy as np
from criterionmethodology import converge
import sys

# names = ["Optsort", "Insertionsort", "Mergesort", "Quicksort"]
# names = ["CopyArray", "Quicksort", "Insertionsort", "Mergesort"]
names = ["Insertionsort"]

# DENSITY = 4
DENSITY = 12
def bounds(name):
    match name:
        case "Insertionsort":
            lo = 3  # 2**n ...
            hi = 12 # for local testing; initially: 16
        case "Quicksort":
            lo = 3
            hi = 22
        case "Mergesort":
            # lo = 12
            lo = 3
            hi = 24
        case "Cilksort":
            # lo = 12
            lo = 3
            hi = 16#24
        case "Optsort":
            lo = 3
            hi = 16#24
        case _:
            lo = 3
            hi = 20
    return lo, hi, (hi-lo)*DENSITY+1

def dotrial(exe, name, size):
    return converge([exe, name, "Seq", str(int(size))])

if __name__ == "__main__":
    exe = sys.argv[1]
    print("Running with executable:", exe)
    for name in names:
        lo, hi, pts = bounds(name)
        with open("%s_out3.csv" % name, "w") as f:
            f.write("# size\tmean\tstddev\tgeomean\tgeostdev\n")
        for i in np.unique(np.logspace(lo, hi, pts, base=2).astype(int)):  # Artem: I don't understand this and I must
            with open("%s_out3.csv" % name, "a") as f:
                f.write("%d" % int(i) + "\t%f\t%f\t%f\t%f\n" % dotrial(exe, name, i))
