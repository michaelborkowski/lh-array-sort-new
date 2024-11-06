#!/usr/bin/env python3
import os
import numpy as np

LO = 8
HI = 16

names = ["Insertionsort", "Quicksort", "Mergesort"]
NAME = names[2]

def dotrial(name, size):
    os.system("criterion-external benchrunner %d Seq %d -- --csv %s.csv" % (name, size, name))
    with open("%s.csv" % name, "r") as f:
        tmp = np.loadtxt(f, delimiter=",", skiprows=1, usecols=1)
        os.remove("%s.csv" % name)
        return tmp

if __name__ == "__main__": 
    np.savetxt(
        "%s%d_out.csv" % (NAME, k), np.array([np.insert(dotrial(NAME, 2**k), 0, int(2**k)) for k in range(LO, HI)])
        , delimiter="\t"
        , header="size\tmean\tmeanLB\tmeanUB\tstddev\tstddevLB\tstddevUB"
    )
