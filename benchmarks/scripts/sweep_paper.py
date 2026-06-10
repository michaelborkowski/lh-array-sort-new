#!/usr/bin/env python3
"""
sweep_paper.py — sequential benchmark sweep for lh-array-sort paper.

Sweeps each algorithm registered in bench_config.ALGOS over log-uniformly
spaced input sizes and collects Criterion mean + CI into per-algorithm CSVs.

Output: benchmarks/data/<algo>_sweep.csv  for each registered algorithm.

To add a new algorithm: edit bench_config.py only.

Usage (from repo root, after cabal configure):
  python3 benchmarks/scripts/sweep_paper.py [--algo NAME] [--dry-run]

Requirements: numpy
"""

import argparse
import csv
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bench_config import ALGOS, AlgoConfig, algo_by_name


# ---------------------------------------------------------------------------
# Core: run bench-criterion once and parse its Criterion CSV output
# ---------------------------------------------------------------------------

def run_criterion(algo_name: str, size: int, csv_path: str,
                  dry_run: bool = False) -> list[dict]:
    """
    Run bench-criterion for `algo_name` at `size`, write Criterion output to
    `csv_path`, and return parsed rows as dicts with keys:
      name, mean_s, ci_lower_s, ci_upper_s
    Returns [] on failure or in dry-run mode.
    """
    cmd = [
        "cabal", "run", "bench-criterion", "--",
        "--size", str(size),
        "--algo", algo_name,
        "--csv", csv_path,
        "-v", "0",
        "+RTS", "-N1", "-RTS",
    ]
    if dry_run:
        print(f"  [dry-run] {' '.join(cmd)}")
        return []

    print(f"  size={size} ... ", end="", flush=True)
    result = subprocess.run(cmd, capture_output=True, text=True)
    if result.returncode != 0:
        print(f"FAILED\n--- stderr ---\n{result.stderr[-1500:]}")
        return []

    rows = []
    try:
        with open(csv_path, newline="") as f:
            for row in csv.DictReader(f):
                rows.append({
                    "name":       row["Name"],
                    "mean_s":     float(row["Mean"]),
                    "ci_lower_s": float(row["MeanLB"]),
                    "ci_upper_s": float(row["MeanUB"]),
                })
        print(f"OK ({len(rows)} rows)")
    except Exception as e:
        print(f"parse error: {e}")
    return rows


# ---------------------------------------------------------------------------
# Sweep driver: iterate over an algo's size grid, append to CSV
# ---------------------------------------------------------------------------

def sweep(algo: AlgoConfig, data_dir: str, dry_run: bool = False):
    out_path = os.path.join(data_dir, algo.seq_csv_name())
    print(f"=== {algo.label} sweep ===")

    done_sizes: set[int] = set()
    if os.path.exists(out_path):
        with open(out_path, newline="") as f:
            for row in csv.DictReader(f):
                done_sizes.add(int(row["size"]))
        print(f"  resuming: {len(done_sizes)} sizes already done")

    is_new = not os.path.exists(out_path)
    with open(out_path, "a" if not is_new else "w", newline="") as f:
        writer = csv.writer(f)
        if is_new:
            writer.writerow(["size", "contestant", "mean_s", "ci_lower_s", "ci_upper_s"])

        for size in algo.sizes():
            if size in done_sizes:
                continue
            with tempfile.NamedTemporaryFile(suffix=".csv", delete=False) as tf:
                tmp = tf.name
            try:
                rows = run_criterion(algo.name, size, tmp, dry_run=dry_run)
            finally:
                if os.path.exists(tmp):
                    os.unlink(tmp)

            for row in rows:
                parts = row["name"].split("/")
                contestant = parts[-1] if len(parts) >= 3 else row["name"]
                writer.writerow([size, contestant,
                                 row["mean_s"], row["ci_lower_s"], row["ci_upper_s"]])
            f.flush()


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Sweep bench-criterion sequentially over input sizes.")
    parser.add_argument("--algo", default="All",
                        help="Algorithm name or 'All' (default: All)")
    parser.add_argument("--dry-run", action="store_true",
                        help="Print commands without executing them.")
    args = parser.parse_args()

    repo_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    data_dir = os.path.join(repo_root, "benchmarks", "data")
    os.makedirs(data_dir, exist_ok=True)
    os.chdir(repo_root)

    algos = ALGOS if args.algo == "All" else [algo_by_name(args.algo)]
    for algo in algos:
        sweep(algo, data_dir, dry_run=args.dry_run)

    print("Done.")


if __name__ == "__main__":
    main()
