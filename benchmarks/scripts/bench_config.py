"""
bench_config.py — central algorithm registry for lh-array-sort benchmarks.

To add a new sorting algorithm:
  1. Add a new AlgoConfig entry to ALGOS below.
  2. That's it — sweep_paper.py, sweep_parallel.py, plot_paper.py, and
     plot_parallel.py all pick it up automatically.
"""

from __future__ import annotations
from dataclasses import dataclass, field
import numpy as np


@dataclass
class AlgoConfig:
    # --- Identity ---
    name: str
    """Criterion --algo value (e.g. "Insertionsort"). Must match bench-criterion CLI."""
    label: str
    """Human-readable label used in plot legends and titles."""

    # --- Sequential sweep ---
    size_lo_exp: float
    """log₂ lower bound for the input-size sweep (inclusive)."""
    size_hi_exp: float
    """log₂ upper bound for the input-size sweep (inclusive)."""
    n_sizes: int
    """Number of log-uniformly spaced sizes between size_lo_exp and size_hi_exp."""
    bar_sizes: list[int]
    """Representative sizes shown in the bar-chart figure (Fig C)."""

    # --- Parallel sweep (optional) ---
    parallel: bool = False
    """Whether this algorithm has a parallel variant to benchmark."""
    par_algo_name: str = ""
    """bench-criterion --algo name for the parallel variant (e.g. "MergesortPar")."""
    par_size: int = 8_000_000
    """Fixed input size used for the parallel core-count sweep."""
    par_cores: list[int] = field(default_factory=lambda: [1, 2, 4, 8, 16])
    """Core counts to sweep for the parallel benchmark."""

    # ------------------------------------------------------------------ helpers

    def sizes(self) -> list[int]:
        """Return the list of input sizes for the sequential sweep."""
        raw = np.logspace(self.size_lo_exp, self.size_hi_exp, self.n_sizes, base=2)
        return sorted(set(int(round(x)) for x in raw))

    def seq_csv_name(self) -> str:
        """Filename (no directory) for the sequential sweep CSV."""
        return self.name.lower() + "_sweep.csv"

    def par_csv_name(self) -> str:
        """Filename (no directory) for the parallel sweep CSV."""
        return self.name.lower() + "_parallel.csv"

    def seq_pdf_name(self) -> str:
        return self.name.lower() + "_sweep.pdf"

    def par_pdf_name(self) -> str:
        return self.name.lower() + "_parallel.pdf"


# ---------------------------------------------------------------------------
# THE REGISTRY — edit only this list to add / remove algorithms.
# ---------------------------------------------------------------------------

ALGOS: list[AlgoConfig] = [
    AlgoConfig(
        name="Insertionsort",
        label="Insertion sort",
        size_lo_exp=3, size_hi_exp=12, n_sizes=37,
        bar_sizes=[100, 1_000],
    ),
    AlgoConfig(
        name="Mergesort",
        label="Merge sort",
        size_lo_exp=10, size_hi_exp=23, n_sizes=27,
        bar_sizes=[100_000, 1_000_000, 8_000_000],
        parallel=True,
        par_algo_name="MergesortPar",
        par_size=8_000_000,
    ),
    AlgoConfig(
        name="Quicksort",
        label="Quicksort",
        size_lo_exp=10, size_hi_exp=23, n_sizes=27,
        bar_sizes=[100_000, 1_000_000, 8_000_000],
    ),
]


def algo_by_name(name: str) -> AlgoConfig:
    """Look up an AlgoConfig by its .name field; raise ValueError if not found."""
    for algo in ALGOS:
        if algo.name == name:
            return algo
    valid = [a.name for a in ALGOS]
    raise ValueError(f"Unknown algorithm {name!r}. Valid names: {valid}")
