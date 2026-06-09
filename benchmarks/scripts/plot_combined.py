#!/usr/bin/env python3
"""
plot_combined.py — combine sweep + parallel speedup graphs on a single PDF page.

Produces:
  plots/combined_sweep_and_parallel.pdf

Layout (2×2):
  top-left:     Insertion sort sweep
  top-right:    Merge sort sweep
  bottom-left:  Quicksort sweep
  bottom-right: Merge sort parallel speedup

Usage (from repo root):
  python3 benchmarks/scripts/plot_combined.py

Requirements: numpy, pandas, matplotlib
"""

import os
import sys

import matplotlib.pyplot as plt
import pandas as pd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bench_config import ALGOS, AlgoConfig

# ---------------------------------------------------------------------------
# Visual constants (kept in sync with plot_paper.py / plot_parallel.py)
# ---------------------------------------------------------------------------

CONTESTANT_COLORS = {
    "ours":   "#0072B2",
    "vector": "#E69F00",
    "c":      "#009E73",
}
CONTESTANT_LABELS = {
    "ours":   "Ours (verified)",
    "vector": "vector-algorithms",
    "c":      "C (stdlib)",
}
CONTESTANT_MARKERS = {
    "ours":   "o",
    "vector": "s",
    "c":      "^",
}


def contestant_display(key: str) -> tuple[str, str, str]:
    k = key.lower()
    return (
        CONTESTANT_LABELS.get(k, key),
        CONTESTANT_COLORS.get(k, "#999999"),
        CONTESTANT_MARKERS.get(k, "D"),
    )


# ---------------------------------------------------------------------------
# Per-subplot drawing helpers (accept an existing Axes object)
# ---------------------------------------------------------------------------

def draw_sweep(ax: plt.Axes, algo: AlgoConfig, data_dir: str) -> bool:
    """Draw a log-log sweep onto *ax*. Returns True if data was found."""
    csv_path = os.path.join(data_dir, algo.seq_csv_name())
    if not os.path.exists(csv_path):
        return False

    df = pd.read_csv(csv_path)
    if df.empty:
        return False

    for contestant, grp in df.groupby("contestant"):
        label, color, marker = contestant_display(contestant)
        grp = grp.sort_values("size")
        ax.fill_between(grp["size"], grp["ci_lower_s"], grp["ci_upper_s"],
                        color=color, alpha=0.2)
        ax.plot(grp["size"], grp["mean_s"], label=label, color=color,
                linewidth=1.5, marker=marker, markersize=3)

    ax.set_xscale("log", base=2)
    ax.set_yscale("log")
    ax.set_xlabel("Input size (N)", fontsize=9)
    ax.set_ylabel("Wall-clock time (s)", fontsize=9)
    ax.legend(fontsize=7)
    ax.tick_params(labelsize=8)
    ax.grid(True, which="both", linestyle="--", linewidth=0.4, alpha=0.6)
    return True


def draw_speedup(ax: plt.Axes, algo: AlgoConfig, data_dir: str) -> bool:
    """Draw parallel speedup onto *ax*. Returns True if data was found."""
    csv_path = os.path.join(data_dir, algo.par_csv_name())
    if not os.path.exists(csv_path):
        return False

    df = pd.read_csv(csv_path).sort_values("cores")
    if df.empty or 1 not in df["cores"].values:
        return False

    t1 = df.loc[df["cores"] == 1, "mean_s"].iloc[0]
    df["speedup"] = t1 / df["mean_s"]
    df["sp_lo"]   = t1 / df["ci_upper_s"]
    df["sp_hi"]   = t1 / df["ci_lower_s"]

    cores = df["cores"].values
    ax.fill_between(cores, df["sp_lo"], df["sp_hi"], alpha=0.2, color="#0072B2")
    ax.plot(cores, df["speedup"], color="#0072B2", linewidth=1.5,
            marker="o", markersize=4, label=f"Par. {algo.label}")
    ax.plot([cores[0], cores[-1]], [cores[0], cores[-1]],
            linestyle="--", color="#999999", linewidth=1.0, label="Ideal")

    ax.set_xlabel("Core count", fontsize=9)
    ax.set_ylabel("Speedup (T₁ / Tₖ)", fontsize=9)
    ax.set_xticks(cores)
    ax.set_xticklabels([str(c) for c in cores])
    ax.legend(fontsize=7)
    ax.tick_params(labelsize=8)
    ax.grid(True, linestyle="--", linewidth=0.4, alpha=0.6)
    return True


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    repo_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    data_dir  = os.path.join(repo_root, "benchmarks", "data")
    plots_dir = os.path.join(repo_root, "plots")
    os.makedirs(plots_dir, exist_ok=True)

    # Collect the three sequential algos (in registry order) and the first
    # parallel algo for the bottom-right panel.
    seq_algos = ALGOS[:3]   # Insertionsort, Mergesort, Quicksort
    par_algos = [a for a in ALGOS if a.parallel]

    fig, axes = plt.subplots(2, 2, figsize=(11, 8), constrained_layout=True)
    (ax_tl, ax_tr), (ax_bl, ax_br) = axes

    panels = [
        (ax_tl, seq_algos[0] if len(seq_algos) > 0 else None, "sweep"),
        (ax_tr, seq_algos[1] if len(seq_algos) > 1 else None, "sweep"),
        (ax_bl, seq_algos[2] if len(seq_algos) > 2 else None, "sweep"),
        (ax_br, par_algos[0] if par_algos else None,          "parallel"),
    ]

    for ax, algo, kind in panels:
        if algo is None:
            ax.set_visible(False)
            continue
        if kind == "sweep":
            draw_sweep(ax, algo, data_dir)
        else:
            draw_speedup(ax, algo, data_dir)

    out = os.path.join(plots_dir, "combined_sweep_and_parallel.pdf")
    fig.savefig(out)
    plt.close(fig)
    print(f"  wrote {out}")


if __name__ == "__main__":
    main()
