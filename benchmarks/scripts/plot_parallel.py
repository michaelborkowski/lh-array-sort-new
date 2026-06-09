#!/usr/bin/env python3
"""
plot_parallel.py — generate parallel speedup figures for the paper.

For each algorithm with parallel=True in bench_config.ALGOS, produces:
  - plots/<algo>_parallel.pdf  (speedup vs core count, one curve per algo)

Also produces a combined comparison figure:
  - plots/parallel_comparison.pdf  (all parallel algos on one set of axes)

To add a new parallel algorithm: edit bench_config.py only.

Usage (from repo root):
  python3 benchmarks/scripts/plot_parallel.py

Requirements: pandas, matplotlib
"""

import os
import sys

import matplotlib.pyplot as plt
import pandas as pd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bench_config import ALGOS, AlgoConfig

# Colour / marker cycle for the combined plot (colour-blind-friendly palette).
_STYLES = [
    {"color": "#0072B2", "marker": "o"},   # blue
    {"color": "#D55E00", "marker": "s"},   # vermillion
    {"color": "#009E73", "marker": "^"},   # green
    {"color": "#CC79A7", "marker": "D"},   # pink
    {"color": "#E69F00", "marker": "v"},   # orange
]


def _load_speedup(algo: AlgoConfig, data_dir: str) -> pd.DataFrame | None:
    """Load a parallel CSV and add speedup columns.  Returns None if unavailable."""
    csv_path = os.path.join(data_dir, algo.par_csv_name())
    if not os.path.exists(csv_path):
        print(f"  [skip] {algo.par_csv_name()} not found")
        return None

    df = pd.read_csv(csv_path).sort_values("cores")
    if df.empty or 1 not in df["cores"].values:
        print(f"  [skip] {algo.par_csv_name()} has no single-core entry (needed for T1)")
        return None

    t1 = df.loc[df["cores"] == 1, "mean_s"].iloc[0]
    df["speedup"] = t1 / df["mean_s"]
    df["sp_lo"]   = t1 / df["ci_upper_s"]
    df["sp_hi"]   = t1 / df["ci_lower_s"]
    return df


def plot_speedup(algo: AlgoConfig, data_dir: str, plots_dir: str):
    """Per-algorithm speedup plot (unchanged from original)."""
    df = _load_speedup(algo, data_dir)
    if df is None:
        return

    fig, ax = plt.subplots(figsize=(4.5, 3.5))
    cores = df["cores"].values
    ax.fill_between(cores, df["sp_lo"], df["sp_hi"], alpha=0.2, color="#0072B2")
    ax.plot(cores, df["speedup"], color="#0072B2", linewidth=1.5,
            marker="o", markersize=4, label=f"Par. {algo.par_algo_name}")
    ax.plot([cores[0], cores[-1]], [cores[0], cores[-1]],
            linestyle="--", color="#999999", linewidth=1.0, label="Ideal")

    ax.set_xlabel("Core count")
    ax.set_ylabel("Speedup (T₁ / Tₖ)")

    ax.set_xticks(cores)
    ax.set_xticklabels([str(c) for c in cores])
    ax.legend(fontsize=8)
    ax.grid(True, linestyle="--", linewidth=0.4, alpha=0.6)
    fig.tight_layout()

    out = os.path.join(plots_dir, algo.par_pdf_name())
    fig.savefig(out)
    plt.close(fig)
    print(f"  wrote {out}")


def plot_combined_speedup(par_algos: list[AlgoConfig], data_dir: str, plots_dir: str):
    """All parallel algorithms on a single speedup plot for easy comparison."""
    fig, ax = plt.subplots(figsize=(6, 4.5))

    all_cores: set[int] = set()
    plotted = 0

    for algo, style in zip(par_algos, _STYLES):
        df = _load_speedup(algo, data_dir)
        if df is None:
            continue

        cores = df["cores"].values
        all_cores.update(cores)

        ax.fill_between(cores, df["sp_lo"], df["sp_hi"],
                        alpha=0.12, color=style["color"])
        ax.plot(cores, df["speedup"],
                color=style["color"], linewidth=1.5,
                marker=style["marker"], markersize=5,
                label=algo.par_algo_name)
        plotted += 1

    if plotted == 0:
        print("  [skip] parallel_comparison.pdf — no data available yet")
        plt.close(fig)
        return

    # Ideal-scaling reference line over the full core range.
    if all_cores:
        lo, hi = min(all_cores), max(all_cores)
        ax.plot([lo, hi], [lo, hi],
                linestyle="--", color="#999999", linewidth=1.0, label="Ideal")

    sorted_cores = sorted(all_cores)
    ax.set_xlabel("Core count")
    ax.set_ylabel("Speedup (T₁ / Tₖ)")

    ax.set_xticks(sorted_cores)
    ax.set_xticklabels([str(c) for c in sorted_cores])
    ax.legend(fontsize=8)
    ax.grid(True, linestyle="--", linewidth=0.4, alpha=0.6)
    fig.tight_layout()

    out = os.path.join(plots_dir, "parallel_comparison.pdf")
    fig.savefig(out)
    plt.close(fig)
    print(f"  wrote {out}")


def main():
    repo_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    data_dir = os.path.join(repo_root, "benchmarks", "data")
    plots_dir = os.path.join(repo_root, "plots")
    os.makedirs(plots_dir, exist_ok=True)

    par_algos = [a for a in ALGOS if a.parallel]
    if not par_algos:
        print("No parallel algorithms registered in bench_config.ALGOS.")
        return

    print("=== Per-algorithm plots ===")
    for algo in par_algos:
        plot_speedup(algo, data_dir, plots_dir)

    print("=== Combined comparison plot ===")
    plot_combined_speedup(par_algos, data_dir, plots_dir)

    print("Done.")


if __name__ == "__main__":
    main()
