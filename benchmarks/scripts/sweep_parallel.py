#!/usr/bin/env python3
"""
sweep_parallel.py — parallel core-count benchmark sweep for lh-array-sort paper.

For each algorithm with parallel=True in bench_config.ALGOS, sweeps across
par_cores core counts at fixed input size par_size.

Output: benchmarks/data/<algo>_parallel.csv  for each parallel algorithm.

To add a new parallel algorithm: edit bench_config.py only.

Usage (from repo root, after cabal configure):
  python3 benchmarks/scripts/sweep_parallel.py [--dry-run]

Requirements: (none beyond stdlib)
"""

import argparse
import csv
import os
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bench_config import ALGOS, AlgoConfig


# ---------------------------------------------------------------------------
# Core: run bench-criterion once and parse Criterion CSV output
# ---------------------------------------------------------------------------

def run_criterion_par(par_algo_name: str, size: int, cores: int,
                      csv_path: str, dry_run: bool = False) -> list[dict]:
    cmd = [
        "cabal", "run", "bench-criterion", "--",
        "--size", str(size),
        "--algo", par_algo_name,
        "--csv", csv_path,
        "-v", "0",
        "+RTS", f"-N{cores}", "-RTS",
    ]
    if dry_run:
        print(f"  [dry-run] {' '.join(cmd)}")
        return []

    print(f"  cores={cores} ... ", end="", flush=True)
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
# Parallel sweep driver
# ---------------------------------------------------------------------------

def sweep_parallel(algo: AlgoConfig, data_dir: str, dry_run: bool = False):
    out_path = os.path.join(data_dir, algo.par_csv_name())
    print(f"=== {algo.label} parallel sweep (size={algo.par_size}) ===")

    done_cores: set[int] = set()
    if os.path.exists(out_path):
        with open(out_path, newline="") as f:
            for row in csv.DictReader(f):
                done_cores.add(int(row["cores"]))
        print(f"  resuming: {len(done_cores)} core counts already done")

    is_new = not os.path.exists(out_path)
    with open(out_path, "a" if not is_new else "w", newline="") as f:
        writer = csv.writer(f)
        if is_new:
            writer.writerow(["cores", "mean_s", "ci_lower_s", "ci_upper_s"])

        for cores in algo.par_cores:
            if cores in done_cores:
                continue
            with tempfile.NamedTemporaryFile(suffix=".csv", delete=False) as tf:
                tmp = tf.name
            try:
                rows = run_criterion_par(algo.par_algo_name, algo.par_size,
                                         cores, tmp, dry_run=dry_run)
            finally:
                if os.path.exists(tmp):
                    os.unlink(tmp)

            for row in rows:
                writer.writerow([cores, row["mean_s"],
                                 row["ci_lower_s"], row["ci_upper_s"]])
            f.flush()


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Sweep bench-criterion over core counts (parallel algorithms).")
    parser.add_argument("--dry-run", action="store_true",
                        help="Print commands without executing them.")
    args = parser.parse_args()

    repo_root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    data_dir = os.path.join(repo_root, "benchmarks", "data")
    os.makedirs(data_dir, exist_ok=True)
    os.chdir(repo_root)

    par_algos = [a for a in ALGOS if a.parallel]
    if not par_algos:
        print("No parallel algorithms registered in bench_config.ALGOS.")
        return

    for algo in par_algos:
        sweep_parallel(algo, data_dir, dry_run=args.dry_run)

    print("Done.")


if __name__ == "__main__":
    main()
