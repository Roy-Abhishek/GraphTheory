"""Optimal sets of [n]^3 (n = 2m + 1) built from the central hexagon plus a gadget at each of six apex corners.

Pattern found at n = 3, 5, 13 (notes/log.md, 2026-10-04): with centered coordinates u in {-m..m}^3 the sources
are all of H = {u : u1 + u2 + u3 = 0} (3m(m+1) + 1 cells, a hexagon through the center) plus m(m+1) more cells,
and T = 3m, the lower bound. The extra cells ("fixers") come in six regions, one at each of the corners with
|sum(u)| = m, e.g. (-m, m, m). In the local frame of the apex (-m, m, m),
    (delta, a, b) = (u1 + m, m - u2, m - u3),
the fixers of the D3d-symmetric solutions at n = 13 are, for every triple 0 <= x <= y <= z <= m = 6,
    (z; 0, 0), (x; 0, 4), (x; 4, 0), (y; 0, 2), (y; 2, 0), (y; 1, 1), (y; 2, 2)
(C(9,3) = 84 solutions; checked against exact.c's exhaustive count). At n = 5 any one cell (c; 0, 0), c = 0..2.

This module searches for such sets: it pins the hexagon, restricts the sources to the hexagon plus a window of
local cells around the apexes (a, b <= a_max, optionally a = b mod 2), imposes D3d symmetry, and asks exact.c for
a labeling of height 3m. A set it finds is valid whatever the window; "no solution" only means none with sources
in the window.

With --face the window is only the six triangular faces {delta = 0, a + b <= m - 1} (the cells the hexagon wave cannot
reach). That is the member (x, y, z) = (0, 0, 0) of the n = 13 family, and the search then takes seconds up to n = 29:
it finds a completion exactly at n = 5, 13, 29 and none at the other n <= 29 (notes/log.md). The n = 29 answer is the
recursive pattern implemented in sage/gadget.py, which builds it directly for n = 2^k - 3.

Run:  python3 sage/hexagon.py 13 17 21 29 [--seconds 600] [--face]
"""

import argparse
import time

import numpy as np

import minperc as mp
import search


def hexagon_mask(n):
    m = (n - 1) // 2
    u = np.arange(n) - m
    return (u[:, None, None] + u[None, :, None] + u[None, None, :]) == 0


def _d3d_closure(base):
    """Union of the images of a boolean mask under the 12 elements of D3d."""
    images, frontier = {base.tobytes(): base}, [base]
    while frontier:
        nxt = []
        for arr in frontier:
            for perm, flips in mp.GROUPS["D3d"]:
                img = np.ascontiguousarray(mp.apply_symmetry(arr, perm, flips))
                if img.tobytes() not in images:
                    images[img.tobytes()] = img
                    nxt.append(img)
        frontier = nxt
    out = np.zeros(base.shape, dtype=bool)
    for img in images.values():
        out |= img
    return out


def window_mask(n, a_max, same_parity=True):
    """D3d images of the local cells (delta, a, b), 0 <= delta <= m, 0 <= a, b <= a_max (a = b mod 2 if same_parity)."""
    m = (n - 1) // 2
    base = np.zeros((n, n, n), dtype=bool)
    for delta in range(m + 1):
        for a in range(a_max + 1):
            for b in range(a_max + 1):
                if same_parity and (a - b) % 2:
                    continue
                base[delta, m - a + m, m - b + m] = True        # u = (delta - m, m - a, m - b), index = u + m
    return _d3d_closure(base)


def face_mask(n):
    """D3d images of the triangle of local cells (0, a, b), a + b <= m - 1: the part of each of the six faces u_i = -+m
    that lies on the far side of the hexagon from the center."""
    m = (n - 1) // 2
    base = np.zeros((n, n, n), dtype=bool)
    for a in range(m):
        for b in range(m - a):
            base[0, m - a + m, m - b + m] = True
    return _d3d_closure(base)


def gadget(mask):
    """The fixers nearest the apex (-m, m, m), in its local frame (delta, a, b), sorted."""
    n = mask.shape[0]
    m = (n - 1) // 2
    cells = [tuple(int(c) - m for c in idx) for idx in np.argwhere(mask & ~hexagon_mask(n))]
    apexes = [(-m, m, m), (m, -m, m), (m, m, -m), (m, -m, -m), (-m, m, -m), (-m, -m, m)]
    near = [c for c in cells if min(range(6), key=lambda i: sum(abs(x - y) for x, y in zip(c, apexes[i]))) == 0]
    return sorted((c[0] + m, m - c[1], m - c[2]) for c in near)


def find(n, a_max=None, same_parity=True, seconds=600, seed=0, restart_base=20000, face=False, count=0):
    """Search for a D3d-symmetric hexagon completion of height 3m. Returns (status, mask or None, seconds).

    face=True allows sources only on the six face triangles (see face_mask). count > 0 enumerates up to that many
    completions instead of stopping at the first one: the result is then (status, number found, seconds), and
    the status is "SAT" with a number below `count` only if that is every completion in the window."""
    m = (n - 1) // 2
    a_max = m - 2 if a_max is None else a_max
    allowed = hexagon_mask(n) | (face_mask(n) if face else window_mask(n, a_max, same_parity))
    forbid = np.flatnonzero(~allowed.ravel())
    pins = np.flatnonzero(hexagon_mask(n).ravel())
    t0 = time.time()
    try:
        status, found, nodes, sols = search.exact((n,) * 3, 3 * m, maxsol=count or 1, pins=pins, orbits=mp.orbits(n, "D3d"),
                                                  forbid=forbid, seed=0 if count else seed, restart_base=restart_base,
                                                  timeout=seconds)
    except Exception:
        return "TIMEOUT", (0 if count else None), time.time() - t0
    for sol in sols:
        mask, T = search.verify(sol, (n,) * 3)
        assert T <= 3 * m and mask.sum() == n * n
    if count:
        return status, len(sols), time.time() - t0
    return status, (search.verify(sols[0], (n,) * 3)[0] if sols else None), time.time() - t0


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("n", type=int, nargs="+")
    parser.add_argument("--seconds", type=float, default=600)
    parser.add_argument("--no-parity", action="store_true", help="do not restrict the window to a = b (mod 2)")
    parser.add_argument("--face", action="store_true", help="sources only on the six face triangles (fast; see docstring)")
    parser.add_argument("--count", type=int, default=0, help="count up to this many completions instead of stopping at one")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    where = "face" if args.face else "window"
    for n in args.n:
        status, result, secs = find(n, same_parity=not args.no_parity, seconds=args.seconds, seed=args.seed, face=args.face,
                                    count=args.count)
        head = f"n={n:3d} (m={(n - 1) // 2}):"
        if args.count:
            print(f"{head} {status}, {result} completions found in the {where} ({secs:.0f}s)", flush=True)
        elif result is None:
            print(f"{head} {status} in {where} ({secs:.0f}s)", flush=True)
        else:
            T = mp.percolates(result)[1]
            print(f"{head} FOUND, T={T} = lower bound {3 * (n - 1) // 2}; gadget (delta, a, b): {gadget(result)} ({secs:.0f}s)", flush=True)


if __name__ == "__main__":
    main()
