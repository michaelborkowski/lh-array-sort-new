#!/usr/bin/env python3
import os
import numpy as np

# names = ["Insertionsort", "Mergesort", "Quicksort", "Optsort"]  # Optsort is piecewise fallback
names = ["Quicksort", "Mergesort"]

# DENSITY = 4
DENSITY = 12
def bounds(name):
    match name:
        case "Insertionsort": # numbers changed due to sorts taking much more time
            lo = 3  # 2**n ...
            hi = 12#16
        case "Quicksort":
            lo = 3
            hi = 16#22
        case "Mergesort":
            # lo = 12
            lo = 3
            hi = 18#24
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

# criterion-external and benchrunner needed locally / on path
def dotrial(name, size):
    os.system("criterion-external benchrunner %s Seq %d -- --csv %s.csv" % (name, size, name))
    with open("%s.csv" % name, "r") as f:
        tmp = np.loadtxt(f, delimiter=",", skiprows=1, usecols=(1,4))
        os.remove("%s.csv" % name)
        return tmp

def dotrial_robust(name, size):
    for _ in range(3):
        t = dotrial(name, size)
        s = tuple(t.tolist())
        if len(s) == 2:
            return t
    return None


if __name__ == "__main__":
    for name in names:
        lo, hi, pts = bounds(name)
        with open("%s_out.csv" % name, "w") as f:
            f.write("# size\tmean\tstddev\n")
        for i in np.logspace(lo, hi, pts, base=2):
            with open("%s_out.csv" % name, "a") as f:
                try:
                    f.write("%d" % int(i) + "\t%f\t%f\n" % tuple(dotrial_robust(name, i).tolist()))
                except:
                    pass
