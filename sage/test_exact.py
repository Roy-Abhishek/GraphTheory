"""Tests for exact.c (via search.exact) and the structure theory in minperc.py, against brute force.

For small boxes every subset of the minimum size (ab + bc + ca) / 3 is simulated directly, and the
number of percolating sets with percolation time <= H must equal the number of solutions exact.c
counts at height H. Covers cubes and non-cubic boxes, a box whose size bound is not an integer (no
exact structure can exist), pinned sources, and a symmetric subspace.

Run:  python3 sage/test_exact.py        (about a minute)
"""

from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path

import numpy as np

import minperc as mp
import search

BOXES = [(2, 2, 2), (1, 3, 3), (1, 4, 4), (2, 2, 5), (2, 3, 3), (1, 3, 6)]    # (ab + bc + ca) divisible by 3
M33 = Path(__file__).resolve().parent.parent / "notes" / "m3-3-classes.json"


def brute_force(dims):
    """{T: number of percolating subsets of the minimum size with that time}; also checks the tight structure."""
    a, b, c = dims
    size = (a * b + b * c + c * a) // 3
    cells = list(product(*(range(s) for s in dims)))
    hist = Counter()
    for subset in combinations(range(len(cells)), size):
        mask = np.zeros(dims, dtype=bool)
        for i in subset:
            mask[cells[i]] = True
        ok, T = mp.percolates(mask)
        if ok:
            hist[T] += 1
            assert mp.exact_structure(mask)[0], f"minimum percolating set of {dims} without the tight structure"
    return hist


def cumulative(hist, H):
    return sum(count for T, count in hist.items() if T <= H)


def test_boxes_against_brute_force():
    for dims in BOXES:
        hist = brute_force(dims)                  # may be empty: the bound (ab + bc + ca)/3 need not be attained
        for H in range(0, max(hist, default=0) + 2):
            status, count, nodes, _ = search.exact(dims, H, maxsol=0)
            assert count == cumulative(hist, H), (dims, H, count, cumulative(hist, H))
            assert (status == "UNSAT") == (count == 0)
        what = f"{sum(hist.values())} percolating minimum sets, T in {sorted(hist)}" if hist else "NO set of the size bound exists"
        print(f"  ok  box {dims}: counts per height match brute force ({what})", flush=True)


def test_non_integer_bound_has_no_exact_structure():
    dims = (2, 2, 3)                              # (4 + 6 + 6) / 3 is not an integer
    for H in range(0, 8):
        assert search.exact(dims, H, maxsol=0)[0] == "UNSAT"
    for size in (5, 6, 7):
        for subset in combinations(range(12), size):
            mask = np.zeros(12, dtype=bool)
            mask[list(subset)] = True
            assert not mp.exact_structure(mask.reshape(dims))[0]
    print("  ok  box (2, 2, 3): no labeling exists and no small subset has the tight structure", flush=True)


def test_pins_against_brute_force():
    dims = (2, 2, 5)
    cells = list(product(*(range(s) for s in dims)))
    size = (4 + 10 + 10) // 3
    for pinned in ([0], [0, 19], [1]):            # corner cells (0,0,0), (1,1,4) and the edge cell (0,0,1)
        expected = Counter()
        for subset in combinations(range(len(cells)), size):
            if not set(pinned) <= set(subset):
                continue
            mask = np.zeros(dims, dtype=bool)
            for i in subset:
                mask[cells[i]] = True
            ok, T = mp.percolates(mask)
            if ok:
                expected[T] += 1
        for H in range(0, max(expected, default=0) + 2):
            count = search.exact(dims, H, maxsol=0, pins=pinned)[1]
            assert count == cumulative(expected, H), (pinned, H, count, cumulative(expected, H))
        print(f"  ok  box {dims} with cells {pinned} forced to be sources: counts match brute force ({sum(expected.values())} sets)", flush=True)


def test_symmetric_subspace_at_n3():
    """Counts of D3d- / S3-invariant minimum sets of [3]^3 from the exhaustive scan vs exact.c on orbits."""
    data = json.loads(M33.read_text())
    syms = mp.cube_symmetries(3)
    invariant = {"D3d": Counter(), "S3": Counter(), "inv": Counter()}
    for row in data["classes"]:
        mask = np.zeros((3, 3, 3), dtype=bool)
        for cell in row["cells"]:
            mask[tuple(i - 1 for i in cell)] = True
        images = {np.ascontiguousarray(s(mask)).tobytes(): np.ascontiguousarray(s(mask)) for s in syms}
        for image in images.values():
            for group in invariant:
                if mp.is_invariant(image, group):
                    invariant[group][row["T"]] += 1
    for group, hist in invariant.items():
        orbits = mp.orbits(3, group)
        for H in range(0, 8):
            count = search.exact((3, 3, 3), H, maxsol=0, orbits=orbits)[1]
            assert count == cumulative(hist, H), (group, H, count, cumulative(hist, H))
        print(f"  ok  [3]^3 {group}-invariant minimum sets: {sum(hist.values())} of 116, counts per height match", flush=True)


def test_known_lower_bounds_are_consistent_with_known_sets():
    """Root propagation says T >= floor(3(n-1)/2); the sets found by search must not beat it and must meet it where known."""
    for n, T_known in ((3, 3), (4, 4), (5, 6), (7, 9)):
        lower = 3 * (n - 1) // 2
        assert search.exact((n,) * 3, lower - 1, maxsol=1, node_limit=1)[0] == "UNSAT", n
        assert T_known >= lower
    print("  ok  root propagation excludes T < floor(3(n-1)/2) for n = 3, 4, 5, 7", flush=True)


def run_all():
    test_boxes_against_brute_force()
    test_non_integer_bound_has_no_exact_structure()
    test_pins_against_brute_force()
    test_symmetric_subspace_at_n3()
    test_known_lower_bounds_are_consistent_with_known_sets()


if __name__ == "__main__":
    run_all()
    print("exact.c agrees with brute force.")
