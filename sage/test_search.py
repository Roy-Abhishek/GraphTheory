"""Tests for the annealer (anneal.c via search.py) against the exhaustive n = 3 ground truth.

The exhaustive scan (exhaustive_m3_3.py, notes/m3-3-classes.json) lists every percolating 9-set of
[3]^3 up to the 48 cube symmetries. Everything the annealer reports must be in that list with the right
time, whatever options are used: plain, with the corner bound, restricted to a symmetry group, and with
pinned sources. Also checks that pinned sources are respected and symmetric search stays symmetric.

Run:  python3 sage/test_search.py        (about 30 s)
"""

import json
from pathlib import Path

import numpy as np

import minperc as mp
import search

M33 = Path(__file__).resolve().parent.parent / "notes" / "m3-3-classes.json"


def known_classes():
    out = {}
    for row in json.loads(M33.read_text())["classes"]:
        mask = np.zeros((3, 3, 3), dtype=bool)
        for cell in row["cells"]:
            mask[tuple(i - 1 for i in cell)] = True
        out[mp.canonical_form(mask)] = row["T"]
    return out


def check_all_known(found, classes):
    for T, mask, labels in found:
        key = mp.canonical_form(mask)
        assert key in classes, "annealer produced a minimum set that is not in the exhaustive list"
        assert classes[key] == T


def run(**kwargs):
    seen = []
    for start in range(0, 120, 12):
        seen += search.search((3, 3, 3), procs=12, seconds=0.15, temp=0.3, H0=7, base_seed=start, verbose=False, **kwargs)
    return seen


def test_plain_and_corner_bound():
    classes = known_classes()
    for corner in (False, True):
        found = run(corner=corner)
        assert found, f"nothing found (corner={corner})"
        check_all_known(found, classes)
        print(f"  ok  corner bound {'on ' if corner else 'off'}: {len(found)} verified sets, all in the exhaustive list with the right T", flush=True)


def test_symmetric_search_stays_symmetric():
    classes = known_classes()
    for group in ("D3d", "S3", "inv", "C3"):
        found = run(orbits=mp.orbits(3, group))
        assert found, group
        check_all_known(found, classes)
        assert all(mp.is_invariant(mask, group) for _, mask, _ in found), group
        print(f"  ok  {group}: {len(found)} sets, all invariant and in the exhaustive list", flush=True)


def test_pinned_sources_are_respected():
    classes = known_classes()
    pins = [0, 26]                                # opposite corners of [3]^3 forced to be sources
    found = run(pins=pins)
    assert found
    check_all_known(found, classes)
    assert all(mask.ravel()[0] and mask.ravel()[26] for _, mask, _ in found)
    print(f"  ok  pinned corners: {len(found)} sets, all contain both corners", flush=True)


def test_optimum_is_reachable():
    found = run(corner=True)
    assert min(T for T, _, _ in found) == 3        # m_3(3) = 3, from the exhaustive scan
    print("  ok  the optimum T = 3 = m_3(3) is found, and nothing below it", flush=True)


def run_all():
    test_plain_and_corner_bound()
    test_symmetric_search_stays_symmetric()
    test_pinned_sources_are_respected()
    test_optimum_is_reachable()


if __name__ == "__main__":
    run_all()
    print("annealer agrees with the exhaustive n = 3 ground truth.")
