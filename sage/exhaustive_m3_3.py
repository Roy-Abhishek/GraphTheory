"""Exact m_3(3) by brute force: the minimum percolation time over ALL 9-subsets of [3]^3.

Simulates every one of the C(27, 9) = 4,686,825 subsets with simulate.py (3-neighbour rule, no
pruning), splitting the work over worker processes. Then, for every percolating set, checks the
structural claims in minperc.py (independent set, exactly 3 earlier neighbours, orientation
by infection time), counts which are Latin squares, and classifies the sets up to the 48 cube
symmetries. Writes one representative per class to notes/m3-3-classes.json.

Run:  python3 sage/exhaustive_m3_3.py        (~30 s on 12 cores)
"""

import json
from collections import Counter
from math import comb
from itertools import combinations, islice
from multiprocessing import Pool
from pathlib import Path
import time

import numpy as np

import minperc as mp
import simulate as sim

CELLS, SIZE, WORKERS = 27, 9, 12
OUT = Path(__file__).resolve().parent.parent / "notes" / "m3-3-classes.json"


def scan(worker):
    """Every WORKERS-th subset, starting at `worker`: ([(bitmask, T) for those that percolate], number examined)."""
    found, examined = [], 0
    flat = np.zeros(CELLS, dtype=bool)
    for comb in islice(combinations(range(CELLS), SIZE), worker, None, WORKERS):
        flat[:] = False
        flat[list(comb)] = True
        examined += 1
        infected, T = sim.simulate(flat.reshape(3, 3, 3), 3, 3)
        if infected:
            found.append((sum(1 << i for i in comb), T))
    return found, examined


def to_mask(bits):
    return np.array([(bits >> i) & 1 for i in range(CELLS)], dtype=bool).reshape(3, 3, 3)


def main():
    start = time.time()
    with Pool(WORKERS) as pool:
        parts = pool.map(scan, range(WORKERS))
    found = [item for part, _ in parts for item in part]
    examined = sum(count for _, count in parts)
    assert examined == comb(CELLS, SIZE), (examined, comb(CELLS, SIZE))
    print(f"scanned all {examined:,} subsets of size {SIZE} in {time.time() - start:.0f}s: {len(found):,} percolate")

    by_T = Counter(T for _, T in found)
    m = min(by_T)
    print("percolation times of the percolating 9-sets:", dict(sorted(by_T.items())))
    print(f"m_3(3) = {m}   ({by_T[m]} sets attain it)")

    # structural claims, on every percolating set
    structure_ok = latin = 0
    classes = {}                                   # canonical form -> [count, T set, representative bits]
    for bits, T in found:
        mask = to_mask(bits)
        ok, why = mp.exact_structure(mask)
        structure_ok += ok
        assert ok, f"percolating 9-set without the tight structure: {why}"
        latin += mp.is_latin(mask)
        key = mp.canonical_form(mask)
        entry = classes.setdefault(key, [0, set(), bits])
        entry[0] += 1
        entry[1].add(T)
    print(f"tight structure (independent, exactly 3 earlier neighbours, no same-round neighbours): "
          f"{structure_ok}/{len(found)} percolating sets")
    print(f"Latin squares among them: {latin}/{len(found)}")
    print(f"{len(classes)} classes under the 48 cube symmetries")

    rows = []
    for key, (count, Ts, bits) in sorted(classes.items(), key=lambda kv: (min(kv[1][1]), -kv[1][0])):
        mask = to_mask(bits)
        assert len(Ts) == 1                       # T is a symmetry invariant
        rows.append({"T": next(iter(Ts)), "sets_in_class": count, "stabilizer": mp.stabilizer_size(mask),
                     "latin": bool(mp.is_latin(mask)),
                     "cells": [[int(c) + 1 for c in idx] for idx in np.argwhere(mask)]})
    for row in rows[:12]:
        print(f"  T={row['T']}  class size {row['sets_in_class']:4d}  stabilizer {row['stabilizer']:2d}  "
              f"Latin={row['latin']}")
    OUT.write_text(json.dumps({"n": 3, "d": 3, "scanned": examined, "percolating": len(found),
                               "histogram_T": dict(sorted(by_T.items())), "classes": rows}, indent=1))
    print(f"wrote {OUT}")


if __name__ == "__main__":
    main()
