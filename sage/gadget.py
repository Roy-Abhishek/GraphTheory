"""Explicit minimum percolating sets of [n]^3 with T = 3(n-1)/2: central hexagon + a recursive face gadget (n = 2^k - 3).

Setting (notes/log.md, 2026-10-04). n = 2m + 1, centered coordinates u in {-m..m}^3, the hexagon H = {u : u1+u2+u3 = 0}
(3m(m+1) + 1 cells), and six apex corners (-m, m, m), (m, -m, m), (m, m, -m) and their negatives. In the local frame
of the apex (-m, m, m),   (delta, a, b) = (u1 + m, m - u2, m - u3),
the triangle {delta = 0, a + b <= m - 1} is the part of the face u1 = -m that the hexagon wave cannot reach (T(m) cells).

The face gadget P(m) is a set of cells (0; a, b) of that triangle, defined for m = 2^j - 2 (m = 0, 2, 6, 14, 30, 62, ...):

    P(0) = {},      P(m) = { (2i, 2j) : i, j >= 0, i + j <= m0 }  U  { (2i + 1, 2j + 1) : (i, j) in P(m0) },   m0 = (m - 2) / 2.

So P(2) = {(0,0)}, P(6) = the six even cells with a + b <= 4 plus (1,1), and the odd cells of P(m) are a copy of P(m0) scaled
by 2 and shifted by (1,1). |P(m)| = m(m+1)/6, hence  |hexagon| + 6 |P(m)| = (2m+1)^2 = n^2.

Theorem (proof in notes/log.md, 2026-10-04): the hexagon plus P(m) at all six apexes percolates in [n]^3 under the
3-neighbour rule in exactly 3m = 3(n-1)/2 rounds, which is the lower bound for this n, so it is a minimum percolating
set of minimum possible percolation time: m_3(n) = 3(n-1)/2 = Theta(n) for n = 2^k - 3. The proof reduces to a 2D
problem on one face triangle, solved by induction on the recursion above (the odd-odd cells of the triangle replay the
m0 problem at double speed), plus the hexagon wave |u1+u2+u3| everywhere else. This module checks every step by computer:
`triangle_labels` runs the 2D process, `labeling`/`check_local_condition` verify the proof's local condition on the whole
cube up to n = 1021, `verify` simulates with two independent simulators up to n = 253.

The rule was read off the solver's answer at n = 29 (sage/hexagon.py with the sources restricted to the faces,
`hexagon.py --face`), which matches it cell for cell; n = 61 and larger were then predictions.

CLI:   python3 sage/gadget.py verify 5 13 29 61 125     (checks size, percolation and T = 3m with two simulators; tight structure when n <= 61)
       python3 sage/gadget.py local 5 13 29 61 125 253 509    (the proof's local condition for the explicit labeling)
       python3 sage/gadget.py family13                  (the 84-triple family at n = 13, see the log)
       python3 sage/gadget.py table 5 13 29 61 125 253 --out notes/family-comparison.csv   (T of the family against the
                                                        residue-class sets of the paper; about 4 minutes)
"""

import argparse
import csv
import itertools
import random
import time

import numpy as np

import minperc as mp

# One frame per apex, (k, i, j, s): s = +1 is the apex with u_k = -m and u_i = u_j = +m (sum = +m), s = -1 its point
# reflection (u_k = +m, u_i = u_j = -m); (i, j) are the other two axes.
APEX_FRAMES = [(k, *[a for a in range(3) if a != k], s) for k in range(3) for s in (+1, -1)]


def hexagon_mask(m):
    u = np.arange(2 * m + 1) - m
    return (u[:, None, None] + u[None, :, None] + u[None, None, :]) == 0


def to_global(frame, local, m):
    """Array index of the cell with local coordinates (delta, a, b) at the given apex of [2m+1]^3."""
    k, i, j, s = frame
    delta, a, b = local
    u = [0, 0, 0]
    if s == +1:
        u[k], u[i], u[j] = delta - m, m - a, m - b
    else:
        u[k], u[i], u[j] = m - delta, a - m, b - m
    return tuple(x + m for x in u)


def valid_m(m):
    """True for m = 0, 2, 6, 14, 30, ...  (m + 2 is a power of 2, or m = 0)."""
    return m == 0 or (m >= 2 and m % 2 == 0 and valid_m((m - 2) // 2))


def positions(m):
    """The set P(m) of (a, b) positions of the face gadget (all on delta = 0), by the recursion in the docstring."""
    if not valid_m(m):
        raise ValueError(f"m = {m}: the recursion needs m = 2^j - 2")
    if m == 0:
        return set()
    m0 = (m - 2) // 2
    even = {(2 * i, 2 * j) for i in range(m0 + 1) for j in range(m0 + 1 - i)}
    odd = {(2 * i + 1, 2 * j + 1) for i, j in positions(m0)}
    return even | odd


def in_gadget(m, a, b):
    """Closed form of P(m): (a, b) is a fixer iff for some l >= 0 both a and b are = 2^l - 1 (mod 2^(l+1)) -- that is, they
    end in exactly l common 1-bits and then a 0-bit each -- and a + b <= m - 2^(l+1). Equals `positions` for m = 2^j - 2."""
    l = 0
    while (1 << (l + 1)) <= m:
        mod = 1 << (l + 1)
        if a % mod == (1 << l) - 1 and b % mod == (1 << l) - 1 and a + b <= m - mod:
            return True
        l += 1
    return False


def triangle_labels(m, gadget=None):
    """Infection round of every cell of the face triangle D_m = {(a, b) : a, b >= 0, a + b <= m - 1}, from the 2D process the
    triangle sees on its own: each cell needs 3 of its 4 in-plane neighbours infected (a neighbour with a negative
    coordinate does not exist), the cells of the hypotenuse a + b = m (the hexagon on this face) are infected from the
    start, and so are the gadget cells (default P(m)); the cell above in the cube never helps, it is infected later.
    Returns an int array L of shape (m + 1, m + 1): L[a, b] = round (0 for sources and hypotenuse), -1 if never
    infected or outside the triangle and its hypotenuse. This is independent of the 3D simulators."""
    gadget = positions(m) if gadget is None else gadget
    a, b = np.indices((m + 1, m + 1))
    triangle = a + b <= m - 1
    infected = (a + b == m)
    for cell in gadget:
        infected[cell] = True
    L = np.where(infected, 0, -1)
    rnd = 0
    while True:
        counts = np.zeros((m + 1, m + 1), dtype=np.int16)
        counts[1:, :] += infected[:-1, :]
        counts[:-1, :] += infected[1:, :]
        counts[:, 1:] += infected[:, :-1]
        counts[:, :-1] += infected[:, 1:]
        new = triangle & ~infected & (counts >= 3)
        if not new.any():
            return L
        rnd += 1
        L[new] = rnd
        infected |= new


def labeling(m):
    """The explicit labeling L of [2m+1]^3 used in the proof: L(u) = |u1+u2+u3| off the six face triangles, and on the
    triangles the labels of the 2D process (triangle_labels), carried to the other five apexes by the symmetries."""
    n = 2 * m + 1
    u = np.arange(n, dtype=np.int16) - m
    L = np.abs(u[:, None, None] + u[None, :, None] + u[None, None, :]).astype(np.int16)
    tri = triangle_labels(m)
    for frame in APEX_FRAMES:
        for a in range(m):
            for b in range(m - a):
                L[to_global(frame, (0, a, b), m)] = tri[a, b]
    return L


def check_local_condition(m):
    """Verify, for the labeling above, that {L = 0} = build(m) and that every cell with L > 0 has at least 3 neighbours with a
    strictly smaller label. That implies (induction on L) that the set percolates in at most max L rounds; max L = 3m.
    Returns max L. Raises AssertionError on failure. A finite check that does not simulate the process."""
    n = 2 * m + 1
    L = labeling(m)
    assert (L == 0).sum() == n * n and ((L == 0) == build(m)).all(), "L = 0 is not the set A"
    smaller = np.zeros(L.shape, dtype=np.int8)
    for axis in range(3):
        lo, hi = [slice(None)] * 3, [slice(None)] * 3
        lo[axis], hi[axis] = slice(0, -1), slice(1, None)
        smaller[tuple(hi)] += (L[tuple(lo)] < L[tuple(hi)])        # neighbour on the low side is earlier
        smaller[tuple(lo)] += (L[tuple(hi)] < L[tuple(lo)])        # neighbour on the high side is earlier
    assert (smaller[L > 0] >= 3).all(), "a cell has fewer than 3 earlier neighbours"
    assert int(L.max()) == 3 * m, int(L.max())
    return int(L.max())


def build(m, gadget=None):
    """Source mask of [2m+1]^3: the hexagon plus, at each apex, the cells (0; a, b) for (a, b) in `gadget` (default P(m))."""
    gadget = positions(m) if gadget is None else gadget
    mask = hexagon_mask(m).copy()
    for frame in APEX_FRAMES:
        for a, b in sorted(gadget):
            idx = to_global(frame, (0, a, b), m)
            assert not mask[idx], "gadget cells overlap"
            mask[idx] = True
    return mask


def verify(m, structure=True, cross_check=True):
    """Check the claim for one m. Returns (|A|, T, seconds). Raises AssertionError if anything fails.

    The time is computed by minperc.percolates and, with cross_check, again by the independent simulate.py; the two must agree."""
    n = 2 * m + 1
    t0 = time.time()
    mask = build(m)
    assert int(mask.sum()) == n * n, "wrong number of sources"
    percolated, T = mp.percolates(mask)
    assert percolated, "does not percolate"
    assert T == 3 * m, f"T = {T}, expected {3 * m}"
    if cross_check:
        import simulate
        assert simulate.simulate(mask, n, 3) == (True, T), "simulate.py disagrees with minperc.py"
    if structure:
        ok, why = mp.exact_structure(mask)
        assert ok, why
    return int(mask.sum()), T, time.time() - t0


# ---------------------------------------------------------------- the n = 13 family of notes/log.md (84 triples)

TRIPLES13 = [t for t in itertools.product(range(7), repeat=3) if t[0] <= t[1] <= t[2]]


def local_cells13(triple):
    x, y, z = triple
    return [(z, 0, 0), (x, 0, 4), (x, 4, 0), (y, 0, 2), (y, 2, 0), (y, 1, 1), (y, 2, 2)]


def build13(triples):
    """n = 13 set: hexagon plus, at apex r, the seven cells local_cells13(triples[r]) (six triples)."""
    mask = hexagon_mask(6).copy()
    for frame, triple in zip(APEX_FRAMES, triples):
        for cell in local_cells13(triple):
            idx = to_global(frame, cell, 6)
            assert not mask[idx], "gadget cells overlap"
            mask[idx] = True
    return mask


def valid13(mask):
    if int(mask.sum()) != 169:
        return False
    percolated, T = mp.percolates(mask)
    return bool(percolated) and T <= 18 and mp.exact_structure(mask)[0]


def family13(random_tuples):
    assert len(TRIPLES13) == 84
    same = sum(valid13(mk) and mp.is_invariant(mk, "D3d") for mk in (build13([t] * 6) for t in TRIPLES13))
    print(f"same triple at all six apexes: {same} of {len(TRIPLES13)} valid and D3d-invariant", flush=True)
    t0, ok, bad = time.time(), 0, 0
    for base, t in itertools.product(TRIPLES13, TRIPLES13):
        for r in range(6):
            ts = [base] * 6
            ts[r] = t
            ok, bad = (ok + 1, bad) if valid13(build13(ts)) else (ok, bad + 1)
    print(f"one apex different from the other five: valid {ok}, invalid {bad} ({time.time() - t0:.0f}s)", flush=True)
    rng = random.Random(0)
    ok, bad, distinct = 0, 0, set()
    for _ in range(random_tuples):
        mask = build13([rng.choice(TRIPLES13) for _ in range(6)])
        if valid13(mask):
            ok += 1
            distinct.add(mask.tobytes())
        else:
            bad += 1
    print(f"independent random triples at the six apexes: valid {ok}, invalid {bad}; distinct valid sets {len(distinct)}")


def table(ns, out, class_limit=61):
    """CSV of T for the family, the canonical set A, the shifted set A' (sweep.py) and the best residue class
    {sum(v) = c mod n}, c = 0..n-1, at each n. Blank where too slow (best class only for n <= class_limit; A and A' only
    for n <= 125)."""
    import sweep
    rows = []
    for n in ns:
        m = (n - 1) // 2
        _, T_family, _ = verify(m, structure=False)
        row = {"n": n, "lower_bound": 3 * (n - 1) // 2, "family": T_family, "shifted": "", "canonical": "", "best_class": ""}
        if n <= 125:
            row["shifted"] = mp.percolates(sweep.shifted(n, 3))[1]
            row["canonical"] = mp.percolates(sweep.canonical(n, 3))[1]
        if n <= class_limit:
            S = sweep.coordinate_sums(n, 3)
            row["best_class"] = min(mp.percolates(S % n == c)[1] for c in range(n))
        rows.append(row)
        print(row, flush=True)
    with open(out, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = parser.add_subparsers(dest="cmd", required=True)
    v = sub.add_parser("verify")
    v.add_argument("n", type=int, nargs="+")
    f = sub.add_parser("family13")
    f.add_argument("--random", type=int, default=4000)
    lc = sub.add_parser("local", help="check the local condition for the explicit labeling (no simulation)")
    lc.add_argument("n", type=int, nargs="+")
    t = sub.add_parser("table")
    t.add_argument("n", type=int, nargs="+")
    t.add_argument("--out", default="family-comparison.csv")
    args = parser.parse_args()
    if args.cmd == "verify":
        for n in args.n:
            m = (n - 1) // 2
            if n % 2 == 0 or not valid_m(m):
                print(f"n = {n}: not of the form 2^k - 3, skipped")
                continue
            size, T, secs = verify(m, structure=n <= 61)
            print(f"n = {n:4d} (m = {m:3d}): |A| = {size} = n^2, percolates, T = {T} = 3(n-1)/2 = lower bound  "
                  f"[|P(m)| = {len(positions(m))}, {secs:.0f}s]", flush=True)
    elif args.cmd == "local":
        for n in args.n:
            t0 = time.time()
            top = check_local_condition((n - 1) // 2)
            print(f"n = {n:4d}: L = 0 exactly on A_n; every other cell has >= 3 earlier neighbours; max L = {top} = 3(n-1)/2 "
                  f"[{time.time() - t0:.0f}s]", flush=True)
    elif args.cmd == "table":
        table(args.n, args.out)
    else:
        family13(args.random)


if __name__ == "__main__":
    main()
