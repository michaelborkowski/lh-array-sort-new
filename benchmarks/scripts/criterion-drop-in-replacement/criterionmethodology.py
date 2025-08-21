#!/usr/bin/env python

#
# The script determines the cost of one iteration of a function (in seconds) using an executable that
#
# - runs `iters` iterations of that function in a tight loop and
# - prints out the time it took to run them.
#
# Example call:
#
#    ./criterionmethodology.py $(cabal list-bin benchrunner) Quicksort Seq 2000
#
# In particular, we
#
# - run given executable (the first and only relevant argument) with 'iters' argument varied from 1 to N;
#   N and the step size are dynamially determined based on the time it takes to run the binary;
# - fetch timing results from binary's stdout and do linear regression over them;
# - plot the regression (see the `plot` function) in `plot.png`.
#
# Growing the `iters` parameter is the main ingenuity of the script. It follows the Criterion methodology:
# running the given binary for small number of iterations doubling them every time, and upon reaching
# a certain threshold (FIRST_ITER_THRESHOLD), increasing them linearly until the overall execution time
# reaches another threshold (TOTAL_TIME_THRESHOLD) seconds.
#
# - The `converge` function runs the whole process, starting with a small number of iterations.
# - The `iter` function encodes the methodology for increasing 'iters'.
# - The `do_bench` function runs the binary and scrapes the output, so the expected binary's interface is encoded in it.
#

import numpy as np
from sys import argv
import subprocess
from time import time
import math

from matplotlib import pyplot as plt

LOG=True
MAKE_PLOT = False
FIRST_ITER_THRESHOLD = 3e-6 # 0.65
TOTAL_TIME_THRESHOLD = 1    # 3.5
                            # ^^ Joseph's original values, but they are too high for my machine.

# Poor-man logging
def log(format, **xs):
    if LOG:
        print(format, **xs)

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

# Do one trial: run the binary with given arguments, including the given `iters`, and return the batch time.
def do_bench(cliargs, iters):
    out = str(subprocess.check_output([cliargs[0], str(iters)] + cliargs[1:]))
    s1 = out[out.find("SELFTIMED")+11:]
    s2 = float(s1[:s1.find("\n")-4])
    selftimed = s2

    b1 = out[out.find("BATCHTIME")+11:]
    b2 = float(b1[:b1.find("SELFTIMED")-2])
    batchtime = b2

    #log(f"ITERS: {iters}, BATCHTIME: {batchtime}, SELFTIMED: {selftimed}")
    return batchtime

# Increase 'iters' and do one trial with that. Store results in xs and ys. Return new iters.
def iter(iters, cliargs, start_time, xs, ys):
    if time() - start_time < TOTAL_TIME_THRESHOLD:
        iters = int(math.trunc(float(iters) * 1.2) + 1)
    else:
        iters += 1 + iters // 20
    log(str(iters) + " ", end="", flush=True)
    st = do_bench(cliargs, iters)
    xs.append(iters)
    ys.append(st)
    return iters

def plot(xs, ys, b, c, m, p):
    plotfile = "plot.png"
    os.remove(plotfile) if os.path.exists(plotfile) else None
    plt.plot(xs, ys, 'rx')
    plt.plot([xs[0], xs[-1]], [m*xs[0]+b, m*xs[-1]+b], color="blue")
    plt.plot(xs, [c*x**p for x in xs], color="green")
    plt.savefig(plotfile)

# Main function to run the iteration experiment.
# - cliargs is a list of command line arguments WIHTOUT the current script's name (argv[0]), in particular:
#   - the first argument is the path to the binary, and
#   - the rest is simply the arguments to pass to the binary.
def converge(cliargs):
    bin = cliargs[0].rsplit('/', 1)[-1] # Get the binary name from the path
    log("Converge on: " + str([bin] + cliargs[1:]))
    log("iters: ", end="")
    xs = []
    ys = []
    iters = 1
    t = time()

    # First find a starting point for `iters` where the time is at least FIRST_ITER_THRESHOLD seconds
    while len(xs) == 0:
        log(str(iters) + " ", end="", flush=True)
        st = do_bench(cliargs, iters)
        if st < FIRST_ITER_THRESHOLD: # Artem: Joseph had `st * iters < ...` here but I think it's a typo
            iters *= 2
            continue
        xs.append(iters)
        ys.append(st)

    log(" | ", end="", flush=True)
    # Do two more trials increasing iters regardless of time
    for _ in range(2):
        iters = iter(iters, cliargs, t, xs, ys)

    log(" | ", end="", flush=True)
    # Keep increasing iters until we reach TOTAL_TIME_THRESHOLD seconds of execution in total
    while time() - t < TOTAL_TIME_THRESHOLD:
        iters = iter(iters, cliargs, t, xs, ys)
    log("done!")

    m, b, sig = linear_regression_with_std(xs, ys)
    p, lnc, lngsd = linear_regression_with_std([math.log(x) for x in xs], [math.log(y) for y in ys])
    c, gsd = math.exp(lnc), math.exp(lngsd)

    log(f"Slope (Mean):     {m:.2e}, Stdev:    {sig:.2e}, Intercept (Overhead): {b:.2e}")
    log(f"Factor (Geomean): {c:.2e}, GeoStdev: {gsd:.2e}, Power (Distortion):   {p:.2e}")

    if MAKE_PLOT:
        plot(xs, ys, b, c, m, p)

    return m, sig, c, gsd

if __name__ == "__main__":
    converge(argv[1:])
