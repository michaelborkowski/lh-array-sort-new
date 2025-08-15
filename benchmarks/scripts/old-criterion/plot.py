#!/usr/bin/env python3
import numpy as np
import matplotlib.pyplot as plt

PATHS = ("Mergesort_out.csv", "Insertionsort_out.csv", "Quicksort_out.csv")

if __name__ == "__main__":
    data = []
    # plt.figure(constrained_layout=True)
    for path in PATHS:
        a = np.genfromtxt(path, skip_header=1)
        data.append(tuple(u.flatten() for u in tuple(np.hsplit(a, 3))))
    for x, y, y_err in data:
        plt.plot(x, y)
    # plt.axvline(1555, color="purple")
    for x, y, y_err in data:
        plt.fill_between(x, y-y_err, y+y_err, alpha=0.2)
    plt.legend(("msort", "isort", "qsort"), loc="lower right")
    plt.xlabel("Array Size (#)")
    plt.ylabel("Time (s)")
    plt.title("Sorting Time vs Array Size")
    plt.yscale("log")
    plt.xscale("log")
    plt.savefig("plot.png")
