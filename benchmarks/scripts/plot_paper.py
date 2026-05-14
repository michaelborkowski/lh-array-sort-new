#!/usr/bin/env python3
"""
plot_paper.py — generate sequential benchmark figures for the paper.

For each algorithm in bench_config.ALGOS, produces:
  - plots/<algo>_sweep.pdf    (log-log wall-clock sweep, Fig A / Fig B per algo)
  - plots/bar_chart.pdf       (grouped bar chart across all algorithms, Fig C)

To add a new algorithm: edit bench_config.py only.

Usage (from repo root):
  python3 benchmarks/scripts/plot_paper.py

Requirements: numpy, pandas, matplotlib
"""

import os
import sys

import matplotlib.pyplot as plt
import numpy as np
import pandas as pd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bench_config import ALGOS, AlgoConfig

# ---------------------------------------------------------------------------
# Visual constants (colour-blind-friendly palette; same across all algorithms)
# ---------------------------------------------------------------------------

CONTESTANT_COLORS = {
    "ours":   "#0072B2",   # blue
    "vector": "#E69F00",   # orange
    "c":      "#009E73",   # green
}
CONTESTANT_LABELS = {
    "ours":   "Ours (verified)",
    "vector": "vector-algorithms",
    "c":      "C (stdlib)",
}
CONTESTANT_MARKERS = {
    "ours":   "o",   # circle
    "vector": "s",   # square
    "c":      "^",   # triangle
}


def contestant_display(key: str) -> tuple[str, str, str]:
    """Return (label, color, marker) for a contestant key (lowercased)."""
    k = key.lower()
    label  = CONTESTANT_LABELS.get(k, key)
    color  = CONTESTANT_COLORS.get(k, "#999999")
    marker = CONTESTANT_MARKERS.get(k, "D")
    return label, color, marker


# ---------------------------------------------------------------------------
# Fig A / B — log-log sweep plot for a single algorithm
# ---------------------------------------------------------------------------

def plot_sweep(algo: AlgoConfig, data_dir: str, plots_dir: str):
    csv_path = os.path.join(data_dir, algo.seq_csv_name())
    if not os.path.exists(csv_path):
        print(f"  [skip] {algo.seq_csv_name()} not found")
        return

    df = pd.read_csv(csv_path)
    if df.empty:
        print(f"  [skip] {algo.seq_csv_name()} is empty")
        return

    fig, ax = plt.subplots(figsize=(5, 3.5))
    for contestant, grp in df.groupby("contestant"):
        label, color, marker = contestant_display(contestant)
        grp = grp.sort_values("size")
        ax.fill_between(grp["size"], grp["ci_lower_s"], grp["ci_upper_s"],
                        color=color, alpha=0.2)
        ax.plot(grp["size"], grp["mean_s"], label=label, color=color,
                linewidth=1.5, marker=marker, markersize=3)

    ax.set_xscale("log", base=2)
    ax.set_yscale("log")
    ax.set_xlabel("Input size (N)")
    ax.set_ylabel("Wall-clock time (s)")
    ax.set_title(algo.label)
    ax.legend(fontsize=8)
    ax.grid(True, which="both", linestyle="--", linewidth=0.4, alpha=0.6)
    fig.tight_layout()

    out = os.path.join(plots_dir, algo.seq_pdf_name())
    fig.savefig(out)
    plt.close(fig)
    print(f"  wrote {out}")


# ---------------------------------------------------------------------------
# Fig C — grouped bar chart across all algorithms
# ---------------------------------------------------------------------------

def plot_bar_chart(plots_dir: str, data_dir: str):
    fig, axes = plt.subplots(1, len(ALGOS),
                             figsize=(4.5 * len(ALGOS), 3.5),
                             sharey=False)
    if len(ALGOS) == 1:
        axes = [axes]

    any_data = False
    for ax, algo in zip(axes, ALGOS):
        csv_path = os.path.join(data_dir, algo.seq_csv_name())
        if not os.path.exists(csv_path):
            ax.set_title(f"{algo.label}\n(no data)")
            continue

        df = pd.read_csv(csv_path)
        df = df[df["size"].isin(algo.bar_sizes)]
        if df.empty:
            ax.set_title(f"{algo.label}\n(no data for bar sizes)")
            continue

        any_data = True
        contestants = df["contestant"].unique().tolist()
        x = np.arange(len(algo.bar_sizes))
        width = 0.8 / max(len(contestants), 1)

        for i, contestant in enumerate(contestants):
            label, color, marker = contestant_display(contestant)
            sub = df[df["contestant"] == contestant].set_index("size")
            means_ms = [sub.loc[s, "mean_s"] * 1000 if s in sub.index else float("nan")
                        for s in algo.bar_sizes]
            ci_lo_ms = [sub.loc[s, "ci_lower_s"] * 1000 if s in sub.index else 0.0
                        for s in algo.bar_sizes]
            ci_hi_ms = [sub.loc[s, "ci_upper_s"] * 1000 if s in sub.index else 0.0
                        for s in algo.bar_sizes]
            yerr = [
                [m - lo for m, lo in zip(means_ms, ci_lo_ms)],
                [hi - m for m, hi in zip(means_ms, ci_hi_ms)],
            ]
            ax.bar(x + i * width, means_ms, width, label=label, color=color,
                   yerr=yerr, capsize=3, error_kw={"linewidth": 0.8})

        ax.set_xticks(x + width * (len(contestants) - 1) / 2)
        ax.set_xticklabels([f"{s:,}" for s in algo.bar_sizes], rotation=30, ha="right")
        ax.set_ylabel("Time (ms)")
        ax.set_title(algo.label)
        ax.legend(fontsize=7)
        ax.grid(axis="y", linestyle="--", linewidth=0.4, alpha=0.6)

    fig.tight_layout()
    if any_data:
        out = os.path.join(plots_dir, "bar_chart.pdf")
        fig.savefig(out)
        print(f"  wrote {out}")
    plt.close(fig)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    repo_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    data_dir = os.path.join(repo_root, "benchmarks", "data")
    plots_dir = os.path.join(repo_root, "plots")
    os.makedirs(plots_dir, exist_ok=True)

    print("=== Sweep plots ===")
    for algo in ALGOS:
        plot_sweep(algo, data_dir, plots_dir)

    print("=== Bar chart ===")
    plot_bar_chart(plots_dir, data_dir)

    print("Done.")


if __name__ == "__main__":
    main()
