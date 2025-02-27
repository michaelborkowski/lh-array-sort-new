import subprocess
import os
import re
import statistics as stat
import matplotlib.pylab as plt

benchrunner_path = "/local/scratch/a/singhav/lh-array-sort/dist-newstyle/build/x86_64-linux/ghc-9.10.1/benchrunner-0.1/x/benchrunner/build/benchrunner/benchrunner"

def run(threads, array_size, modes, benchmarks, iterations):

    for bench in benchmarks:
        for size in array_size:
            results = {}
            for mode in modes:

                threads_default = ["1"]
                if (mode == "Par"):
                    threads_default = threads

                for thread in threads_default:

                    f = open("out.txt", "w")

                    #./benchrunner 1 Mergesort Par 10000 +RTS -N4
                    command = [benchrunner_path, iterations, bench, mode, size, "+RTS", "-N" + str(thread)]
                    print("Running command:\n")
                    print(" ".join(command) + "\n")

                    subprocess.run(command, stdout=f, text=True)

                    f.close()

                    #read file
                    fr = open("out.txt", "r")
                    lines = fr.readlines()

                    runtimes = []
                    for line in lines:
                        print(line)
                        time = re.search(r"iter time: ([-+]?\d*\.?\d+(?:[eE][-+]?\d+)?\b)", line)

                        if time:
                            print(time[1])
                            runtimes.append(float(time[1]))
                    print(runtimes)

                    key = (bench, mode, size, thread)
                    results[key] = runtimes


            make_plots(results, [bench], threads, [size])



def make_plots(results, benchmarks, threads, inputs):


    for bench in benchmarks:

        for input in inputs:

            plot_inputs = {}
            seq_key = (bench, "Seq", input, "1")
            seq_runtimes = results[seq_key]
            seq_mean = stat.mean(seq_runtimes)

            for thread in threads:

                par_key = (bench, "Par", input, thread)
                par_runtimes = results[par_key]
                par_mean = stat.mean(par_runtimes)

                plot_inputs[int(thread)] = seq_mean / par_mean


            #plot
            plot(plot_inputs, bench, input)



def plot(plot_inputs, bench, input):

    plt.figure()
    lists = sorted(plot_inputs.items())
    x, y = zip(*lists)
    plt.plot(x, y)
    plt.xlabel("Threads")
    plt.ylabel("Speedup")
    plt.title(bench + " Parallel speedup for input: " + input)

    if not os.path.isdir("./plots"):
        os.mkdir("./plots")

    plt.savefig("./plots/" + bench + "_" + input + ".pdf")


if __name__ == "__main__":

    threads = ["1", "2", "4", "8", "16", "32", "64", "128"]
    inputs = ["10", "100", "1000", "10000", "100000", "1000000"]
    modes = ["Seq", "Par"]
    benchmarks = ["Mergesort"]
    iterations = "9"

    run(threads, inputs, modes, benchmarks, iterations)
