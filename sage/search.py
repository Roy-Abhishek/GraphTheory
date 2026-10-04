"""Heuristic search for minimum-size percolating sets of a box with small percolation time (d = 3).

A minimum percolating set of the box a x b x c (size (ab + bc + ca) / 3) is exactly the source set
of an acyclic orientation of the grid with every in-degree 0 or 3, and its time is the longest
directed path (minperc.py, verified exhaustively at n = 3). So the search runs on level labelings
t: cells -> {0..H} with distinct labels on adjacent cells and exactly 0 or 3 smaller-labelled
neighbours per cell; anneal.c anneals those and steps H down after every solution.

Every labeling the C code reports is re-verified here from scratch: the source set is rebuilt, run
through the numpy percolation (minperc.infection_times), and must percolate with the claimed time.

Usage (python API): see main(); CLI: python3 sage/search.py 5 --seconds 120
"""

import argparse
import json
import subprocess
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import numpy as np

import minperc as mp

SRC = Path(__file__).resolve().parent / "anneal.c"
BIN = Path(tempfile.gettempdir()) / "percolation-anneal" / "anneal"
EXACT_SRC = Path(__file__).resolve().parent / "exact.c"
EXACT_BIN = Path(tempfile.gettempdir()) / "percolation-anneal" / "exact"
MOVES_PER_SECOND = 2.0e7          # rough speed of anneal.c on one core, used to turn seconds into budgets


def build(src=SRC, binary=BIN):
    """Compile a C source (cached in the system temp dir) if the binary is missing or out of date."""
    if not binary.exists() or binary.stat().st_mtime < src.stat().st_mtime:
        binary.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["cc", "-O3", "-march=native", "-o", str(binary), str(src), "-lm"], check=True)
    return binary


def exact(dims, H, maxsol=1, node_limit=0, pins=None, orbits=None, timeout=None, seed=0, restart_base=2000,
          forbid=None):
    """Exhaustive search with exact.c for a labeling of height <= H (a minimum percolating set with T <= H).

    Returns (status, count, nodes, solutions): status "SAT", "UNSAT" (proved: none exists) or "LIMIT"
    (node limit hit, inconclusive); solutions = list of label arrays (at most `maxsol`; 0 = count all
    but keep none, to save memory). count = solutions found. A nonzero `seed` switches to restart mode
    (randomised DFS with growing node limits, for finding one solution; UNSAT answers remain proofs).
    """
    build(EXACT_SRC, EXACT_BIN)
    with tempfile.TemporaryDirectory() as tmp:
        pin_arg, orbit_arg = "-", "-"
        if pins is not None and len(pins):
            pin_arg = str(Path(tmp) / "pins.txt")
            Path(pin_arg).write_text(" ".join(str(int(v)) for v in pins))
        if orbits is not None:
            orbit_arg = str(Path(tmp) / "orbits.txt")
            Path(orbit_arg).write_text(f"{len(orbits)}\n" + "\n".join(f"{len(o)} " + " ".join(map(str, o)) for o in orbits))
        forbid_arg = "-"
        if forbid is not None and len(forbid):
            forbid_arg = str(Path(tmp) / "forbid.txt")
            Path(forbid_arg).write_text(" ".join(str(int(v)) for v in forbid))
        out = subprocess.run([str(EXACT_BIN), *map(str, dims), str(H), str(maxsol), str(node_limit), pin_arg, orbit_arg,
                              str(seed), str(restart_base), forbid_arg],
                             capture_output=True, text=True, check=True, timeout=timeout).stdout.split("\n")
    solutions, status, count, nodes, i = [], None, 0, 0, 0
    while i < len(out):
        parts = out[i].split()
        if parts and parts[0] == "SOLUTION":
            solutions.append(np.array(out[i + 1].split(), dtype=np.int16))
            i += 2
            continue
        if parts and parts[0] == "NODES":
            nodes = int(parts[1])
        elif parts and parts[0] in ("SAT", "LIMIT"):
            status, count = parts[0], int(parts[1])
        elif parts and parts[0] == "UNSAT":
            status = "UNSAT"
        i += 1
    return status, count, nodes, solutions


def verify(labels, dims):
    """Rebuild the source set of a level labeling and check it from scratch.

    Returns (source mask, T) where T is the percolation time simulated from the mask alone. Raises
    AssertionError if the labeling is not a valid orientation or the set does not percolate.
    """
    labels = np.asarray(labels).reshape(dims)
    earlier, equal = mp.neighbour_time_counts(labels)
    assert not equal.any(), "adjacent cells share a label"
    assert ((earlier == 0) | (earlier == 3)).all(), "in-degree not in {0, 3}"
    sources = earlier == 0
    a, b, c = dims
    assert 3 * int(sources.sum()) == a * b + b * c + c * a, "wrong number of sources"
    ok, why = mp.exact_structure(sources)
    assert ok, why
    percolated, T = mp.percolates(sources)
    assert percolated and T <= labels.max()
    return sources, T


def corner_distance(dims):
    """Manhattan distance of every cell of the box to its nearest corner."""
    axes = [np.minimum(np.arange(s), s - 1 - np.arange(s)) for s in dims]
    return axes[0][:, None, None] + axes[1][None, :, None] + axes[2][None, None, :]


def radial_labels(dims, H):
    """The largest labeling allowed at height H: label(v) = H - (distance to the nearest corner), which for odd n
    and H = 3(n-1)/2 is the Manhattan distance from the center. Valid except on the central planes."""
    return np.maximum(H - corner_distance(dims), 0)


def attempt(dims, H0, seed, budget, temp, init=None, pins=None, orbits=None, corner=False):
    """One run of anneal.c. Returns (solutions, status): solutions = [(target H, T, moves, labels)] in the
    order found (T strictly decreasing), status = ("STUCK", H, best energy, moves) or None if it ended.
    corner=True confines every label to 0 .. H - (distance to the nearest corner), a sound restriction."""
    build()
    with tempfile.TemporaryDirectory() as tmp:
        init_arg, pin_arg = "-", "-"
        if init is not None:
            init_arg = str(Path(tmp) / "init.txt")
            Path(init_arg).write_text(" ".join(str(int(v)) for v in np.asarray(init).ravel()))
        if pins is not None and len(pins):
            pin_arg = str(Path(tmp) / "pins.txt")
            Path(pin_arg).write_text(" ".join(str(int(v)) for v in pins))
        orbit_arg = "-"
        if orbits is not None:
            orbit_arg = str(Path(tmp) / "orbits.txt")
            Path(orbit_arg).write_text(f"{len(orbits)}\n" + "\n".join(f"{len(o)} " + " ".join(map(str, o)) for o in orbits))
        out = subprocess.run([str(BIN), *map(str, dims), str(H0), str(seed), str(int(budget)), str(temp),
                              init_arg, pin_arg, orbit_arg] + (["corner"] if corner else []),
                             capture_output=True, text=True, check=True).stdout.split("\n")
    solutions, status, i = [], None, 0
    while i < len(out):
        parts = out[i].split()
        if parts and parts[0] == "SOLVED":
            labels = np.array(out[i + 1].split(), dtype=np.int16)
            solutions.append((int(parts[1]), int(parts[2]), int(parts[3]), labels))
            i += 2
        else:
            if parts and parts[0] == "STUCK":
                status = ("STUCK", int(parts[1]), int(parts[2]), int(parts[3]))
            i += 1
    return solutions, status


def search(dims, procs=12, seconds=60.0, temp=0.3, H0=None, init=None, pins=None, base_seed=0, rounds=1,
           verbose=True, orbits=None, corner=False):
    """Run `procs` annealers in parallel for about `seconds` per round, `rounds` rounds.

    Round 1 starts from `init` (a labeling) or from random labels with maximum label H0. Each later
    round restarts every process from the best labeling found so far (fresh seeds). Returns the
    list of every verified distinct solution as (T, source mask, labels), best first.
    """
    build()
    budget = seconds * MOVES_PER_SECOND
    found = {}                                        # source-mask bytes -> (T, mask, labels)
    best = None
    for rnd in range(rounds):
        start = best[2] if best is not None else init
        H = (int(best[0]) if best is not None else (H0 or 3 * max(dims))) if start is None else (H0 or int(np.max(start)))
        jobs = [(dims, H, base_seed + 1000 * rnd + k, budget, temp, start, pins, orbits, corner) for k in range(procs)]
        with ThreadPoolExecutor(max_workers=procs) as pool:
            results = list(pool.map(lambda job: attempt(*job), jobs))
        for k, (solutions, status) in enumerate(results):
            for target, T, moves, labels in solutions:
                mask, T_sim = verify(labels, dims)
                assert T_sim == T, (T_sim, T)
                found.setdefault(mask.tobytes(), (T, mask, labels))
                if best is None or T < best[0]:
                    best = (T, mask, labels)
        if verbose:
            Ts = sorted(r[0][-1][1] for r in results if r[0])
            print(f"round {rnd + 1}: best T so far {best[0] if best else None}; per-process final T {Ts}", flush=True)
    return sorted(found.values(), key=lambda item: item[0])


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("n", type=int, help="side of the cube [n]^3")
    parser.add_argument("--seconds", type=float, default=60.0, help="per round, per process")
    parser.add_argument("--rounds", type=int, default=1)
    parser.add_argument("--procs", type=int, default=12)
    parser.add_argument("--temp", type=float, default=0.3)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--start", choices=["random", "radial", "best-class"], default="random",
                        help="radial: labels H - (distance to the nearest corner); best-class: the sum(u) = (n+3)/2 mod n "
                             "residue class (odd n), the start that reached T = 9 at n = 7")
    parser.add_argument("--H0", type=int, default=None, help="starting height (default 3n for random, floor(3(n-1)/2) for radial)")
    parser.add_argument("--corner", action="store_true", help="confine labels to 0 .. H - (distance to the nearest corner)")
    parser.add_argument("--group", choices=sorted(mp.GROUPS), default="none", help="restrict to sets invariant under this symmetry group")
    parser.add_argument("--out", type=Path, default=None, help="write the best sets as JSON")
    args = parser.parse_args()
    dims = (args.n,) * 3
    init, H0 = None, args.H0
    if args.start == "radial":
        H0 = H0 or 3 * (args.n - 1) // 2
        init = radial_labels(dims, H0)
    elif args.start == "best-class":
        import sweep                                    # imported here: only this start needs it
        init = mp.infection_times(sweep.coordinate_sums(args.n, 3) % args.n == (args.n + 3) // 2)[0]
    orbits = mp.orbits(args.n, args.group) if args.group != "none" else None
    t0 = time.time()
    found = search(dims, args.procs, args.seconds, args.temp, H0=H0, init=init, base_seed=args.seed, rounds=args.rounds,
                   orbits=orbits, corner=args.corner)
    if not found:
        print(f"no valid set found; {time.time() - t0:.0f}s")
        return
    print(f"{len(found)} distinct verified sets; best T = {found[0][0]}; {time.time() - t0:.0f}s")
    if args.out:
        args.out.write_text(json.dumps([{"T": T, "cells": [[int(c) + 1 for c in idx] for idx in np.argwhere(mask)]}
                                        for T, mask, _ in found[:50]], indent=1))


if __name__ == "__main__":
    main()
