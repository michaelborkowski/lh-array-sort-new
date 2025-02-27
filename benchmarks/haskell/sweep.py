#!/usr/bin/env python3
import os
import numpy as np

names = ["Insertionsort", "Quicksort", "Mergesort"]

DENSITY = 4
def bounds(name):
    match name:
        case "Insertionsort":
            lo = 3  # 2**n ...
            hi = 16
        case "Quicksort":
            lo = 3
            hi = 22
        case "Mergesort":
            lo = 12
            hi = 24
    return lo, hi, (hi-lo)*DENSITY+1

def dotrial(name, size):
    os.system("criterion-external benchrunner %s Seq %d -- --csv %s.csv" % (name, size, name))
    with open("%s.csv" % name, "r") as f:
        tmp = np.loadtxt(f, delimiter=",", skiprows=1, usecols=(1,4))
        os.remove("%s.csv" % name)
        return tmp

if __name__ == "__main__":
    for name in names:
        lo, hi, pts = bounds(name)
        np.savetxt(
            "%s_out.csv" % name, np.array([np.insert(dotrial(name, i), 0, int(i)) for i in np.logspace(lo, hi, pts, base=2)])
            , delimiter="\t"
            # , header="size\tmean\tmeanLB\tmeanUB\tstddev\tstddevLB\tstddevUB"
            , header="size\tmean\tstddev"
        )
