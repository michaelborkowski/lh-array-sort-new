#!/usr/bin/env python3
import numpy as np
import matplotlib.pyplot as plt

SLOWPATH = "Mergesort_out.csv"
FASTPATH = "sort_merge_seq_out.csv"

def read(): 
    slow = np.genfromtxt(SLOWPATH, skip_header=1)
    fast = np.genfromtxt(FASTPATH, skip_header=1)
    return slow, fast

def plot(slow, fast): 
    fast = fast[:171]
    x = slow[:,0]  # assume same x values
    speedup = slow[:,1] / fast[:,1]
    # plt.figure(constrained_layout=True)
    plt.plot(x, speedup)
    plt.xlabel("Array Size (#)")
    plt.ylabel("Speedup")
    plt.title("Speedup")
    plt.yscale("log")
    plt.xscale("log")
    plt.savefig("c_vs_ghc.png")

if __name__ == "__main__":
    slow, fast = read()
    plot(slow, fast)
