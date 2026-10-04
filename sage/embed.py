"""Padding / embedding experiments (refs/code-context.md, line of attack 2), d = 3.

Take the fast recursive set R_c of [N]^3, N = 2^p > n (the nim-sum sets {x : x1^x2^x3 = c}, one per
parity choice c in 0..N-1), and adapt it down to [n]^3 by restricting to a sub-box. What survives is
too small to percolate by itself (a minimum set of [n]^3 has n^2 cells; the restriction keeps about
n^3 / N). The exact solver then answers precisely how far the restriction is from a real answer:
  - extendable?  does ANY minimum percolating set of [n]^3 contain the surviving sources (they are
    pinned), and
  - best time    the smallest T of such an extension that pinned annealing finds (an upper bound).

`python3 sage/embed.py restrict` prints the table; `python3 sage/embed.py boxes` lists which small
boxes a x b x c admit a percolating set of the perimeter-bound size at all, which decides whether an
unequal split of the recursion (n = a + b) can work.
"""

import argparse
import time

import numpy as np

import minperc as mp
import search
import sweep


def restrictions(n, N):
    """Every restriction of every R_c (c in 0..N-1) to a sub-box of side n, as (c, offset, boolean n-cube)."""
    for c in range(N):
        R = sweep.xor_set(N, 3, c)
        for o in np.ndindex(*(N - n + 1,) * 3):
            yield c, o, R[o[0]:o[0] + n, o[1]:o[1] + n, o[2]:o[2] + n].copy()


def anneal_extension(n, mask, seconds, procs=6):
    """Upper bound on the best extension of the sources in `mask` to a minimum percolating set of [n]^3.

    Pinned, corner-bounded annealing from the radial labeling (the method that finds optimal sets at n = 5, 7).
    Returns the smallest T found, or None. None is evidence that no extension exists, not a proof."""
    dims = (n,) * 3
    pins = [int(i) for i in np.flatnonzero(mask.ravel())]
    H0 = 3 * ((n - 1) // 2) + 8
    best = None
    for temp in (0.25, 0.35):
        found = search.search(dims, procs=procs, seconds=seconds, temp=temp, H0=H0, init=search.radial_labels(dims, H0),
                              pins=pins, corner=True, verbose=False)
        if found and (best is None or found[0][0] < best):
            best = found[0][0]
    return best


def restrict_table(n, keep, seconds):
    N = 1 << n.bit_length()
    m = (n - 1) // 2
    print(f"\n=== n={n} embedded in N={N}: {N} parity variants x {(N - n + 1) ** 3} sub-boxes; need {n * n} sources, lower bound T >= {3 * (n - 1) // 2} ===")
    seen, rows = set(), []
    for c, o, mask in restrictions(n, N):
        key = mp.canonical_form(mask)
        if key in seen:
            continue
        seen.add(key)
        times, _ = mp.infection_times(mask)
        rows.append((int(mask.sum()), float((times >= 0).mean()), c, o, mask))
    rows.sort(key=lambda r: -r[0])
    print(f"{len(rows)} restrictions up to cube symmetry; sources kept (max {rows[0][0]}, min {rows[-1][0]}) of the {n * n} needed")
    print("  kept  needed-more  infected-from-it-alone  c   offset      best extension T (lower bound %d)" % (3 * m))
    for kept, frac, c, o, mask in rows[:keep]:
        t0 = time.time()
        T = anneal_extension(n, mask, seconds)
        res = f"extension found, T = {T}" if T is not None else "no extension found by pinned annealing"
        print(f"  {kept:4d}  {n * n - kept:6d}       {frac:6.1%}               {c:2d}  {o}   {res}   ({time.time() - t0:.0f}s)", flush=True)


def box_table(max_side):
    """For boxes a <= b <= c <= max_side with (ab + bc + ca) divisible by 3: is there ANY percolating set of size
    (ab + bc + ca) / 3 (exhaustive, via the exact solver with H large), and if so its minimum T."""
    print("box a x b x c: size bound, and the smallest T of a minimum percolating set ('-' = none exists)")
    for a in range(1, max_side + 1):
        for b in range(a, max_side + 1):
            for c in range(b, max_side + 1):
                q = a * b + b * c + c * a
                if q % 3:
                    continue
                best = "-"
                for H in range(1, a + b + c + 4):
                    status, count, nodes, sols = search.exact((a, b, c), H, maxsol=1, node_limit=2_000_000, timeout=60)
                    if status == "SAT":
                        best = str(H)
                        break
                    if status == "LIMIT":
                        best = "?"
                        break
                print(f"  {a} x {b} x {c}: size {q // 3:3d}   min T = {best}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("what", choices=["restrict", "boxes"])
    parser.add_argument("--n", type=int, nargs="*", default=[5, 7, 11])
    parser.add_argument("--keep", type=int, default=8, help="restrictions (largest first) to extend")
    parser.add_argument("--seconds", type=float, default=20, help="annealing time per temperature")
    parser.add_argument("--max-side", type=int, default=6)
    args = parser.parse_args()
    if args.what == "restrict":
        for n in args.n:
            restrict_table(n, args.keep, args.seconds)
    else:
        box_table(args.max_side)


if __name__ == "__main__":
    main()
