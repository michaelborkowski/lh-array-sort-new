#!/usr/bin/env python3
import numpy as np
from sys import argv
import subprocess
from time import time
import math

from matplotlib import pyplot as plt

MAKE_PLOT = False

def linear_regression_with_std(x, y):
    x = np.array(x)
    y = np.array(y)
    x_mean = np.mean(x)
    y_mean = np.mean(y)
    numerator = np.sum((x - x_mean) * (y - y_mean))
    denominator = np.sum((x - x_mean) ** 2)
    slope = numerator / denominator
    intercept = y_mean - slope * x_mean
    y_pred = slope * x + intercept
    residuals = y - y_pred
    std_dev = np.std(residuals)
    return slope, intercept, std_dev

def do_bench(cliargs, iters): 
    print([cliargs[1], str(iters)] + cliargs[2:])
    out = str(subprocess.check_output([cliargs[1], str(iters)] + cliargs[2:]))
    s1 = out[out.find("SELFTIMED")+11:]
    s2 = float(s1[:s1.find("\n")-4])
    selftimed = s2

    b1 = out[out.find("BATCHTIME")+11:]
    b2 = float(b1[:b1.find("SELFTIMED")-2])
    batchtime = b2

    print(f"ITERS: {iters}, BATCHTIME: {batchtime}, SELFTIMED: {selftimed}")
    return batchtime

def converge(cliargs): 
    xs = []
    ys = []
    iters = 1
    t = time()
    while len(xs) == 0: 
        st = do_bench(cliargs, iters)
        if st * iters < 0.65: 
            iters *= 2
            continue
        xs.append(iters)
        ys.append(st)
    for _ in range(2): 
        if time() - t < 3.5: 
            iters = int(math.trunc(float(iters) * 1.2) + 1)
        else: 
            iters += 1 + iters // 20
        st = do_bench(cliargs, iters)
        xs.append(iters)
        ys.append(st)
    while time() - t < 3.5: 
        if time() - t < 3.5: 
            iters = int(math.trunc(float(iters) * 1.2) + 1)
        else: 
            iters += 1 + iters // 20
        st = do_bench(cliargs, iters)
        xs.append(iters)
        ys.append(st)
    m, b, sigma = linear_regression_with_std(xs, ys)
    print(f"Slope (Mean): {m}, Intercept (Overhead): {b}, Stdev: {sigma}")
    p, lnc, lngsd = linear_regression_with_std([math.log(x) for x in xs], [math.log(y) for y in ys])
    c, gsd = math.exp(lnc), math.exp(lngsd)
    print(f"Power (Distortion): {p}, Factor (Geomean) {c}, GeoStdev {gsd}")
    if MAKE_PLOT: 
        plt.plot(xs, ys, 'rx')
        plt.plot([xs[0], xs[-1]], [m*xs[0]+b, m*xs[-1]+b], color="blue")
        plt.plot(xs, [c*x**p for x in xs], color="green")
        plt.savefig("plot.png")
    return m, sigma, c, gsd

if __name__ == "__main__": 
    print(converge(argv))
