"""Regenerate the best minimum percolating sets of [n]^3 found so far, verify them, and store them.

Each set has exactly n^2 cells and is rebuilt here with the exact solver (search.exact), using the
height H, symmetry group and random seed that found it. Every set is then re-verified twice, by the
numpy percolation (search.verify, which also checks the tight orientation structure) and by the pure
Python brute-force simulator (hand_verify.percolate), so the file does not depend on the solver being
right. T is the simulated percolation time, which can be below H.

lower bound: T >= floor(3(n-1)/2) for every n (root propagation in exact.c, checked in test_exact.py;
for odd n it is the one-line argument that every directed path ends at a corner, and the center
cell is at Manhattan distance 3(n-1)/2 from all corners).

Run:  python3 sage/best_sets.py        (writes notes/best-sets-d3.json; a few minutes)
"""

import json
from pathlib import Path
import time

import numpy as np

import hand_verify as hv
import minperc as mp
import search
import sweep

OUT = Path(__file__).resolve().parent.parent / "notes" / "best-sets-d3.json"

# (n, H, symmetry group or None, maxsol, restart seed, restart base): the exact-solver call that found the set
CASES = [
    (4, 4, None, 2, 0, 0),
    (5, 6, "D3d", 3, 0, 0),
    (6, 7, None, 1, 0, 0),
    (7, 9, "D3d", 1, 0, 0),
    (9, 14, "D3d", 3, 0, 0),
    (11, 17, "D3d", 1, 1, 20000),
    (13, 19, "D3d", 1, 0, 0),
]


def record(n, mask, how):
    T = mp.percolates(mask)[1]
    cells = {tuple(int(c) + 1 for c in idx) for idx in np.argwhere(mask)}
    if n <= 13:
        infected, rounds = hv.percolate(cells, n, 3)           # independent brute-force check
        assert len(infected) == n ** 3 and rounds == T
    best_class = sweep.coordinate_sums(n, 3) % n == (n + 3) // 2
    return {"n": n, "T": T, "lower_bound": 3 * (n - 1) // 2, "method": how,
            "best_residue_class_T": mp.percolates(best_class)[1] if n % 2 else None,
            "shifted_set_T": mp.percolates(sweep.shifted(n, 3))[1],
            "latin": bool(mp.is_latin(mask)), "stabilizer": mp.stabilizer_size(mask),
            "cells": [list(c) for c in sorted(cells)]}


def main():
    results = []
    # n = 3: the exhaustive scan (exhaustive_m3_3.py) found one class with T = 3
    data = json.loads((OUT.parent / "m3-3-classes.json").read_text())
    row = next(r for r in data["classes"] if r["T"] == 3)
    mask = np.zeros((3, 3, 3), dtype=bool)
    for c in row["cells"]:
        mask[tuple(i - 1 for i in c)] = True
    results.append(record(3, mask, "exhaustive scan of all 4,686,825 nine-subsets"))
    for n, H, group, maxsol, seed, base in CASES:
        t0 = time.time()
        orbits = mp.orbits(n, group) if group else None
        status, count, nodes, sols = search.exact((n,) * 3, H, maxsol=maxsol, orbits=orbits, seed=seed, restart_base=base)
        assert status == "SAT" and sols, (n, H, status)
        mask, T = search.verify(sols[0], (n,) * 3)
        how = f"exact.c, H={H}, symmetry {group or 'none'}" + (f", restart seed {seed}" if seed else "")
        results.append(record(n, mask, how))
        print(f"n={n:2d}: T={T:2d} (lower bound {3 * (n - 1) // 2}) from {how} ({time.time() - t0:.0f}s)", flush=True)
    OUT.write_text(json.dumps(results, indent=1))
    print(f"wrote {OUT}")


if __name__ == "__main__":
    main()
