"""Sweep T(A) over candidate optimal-size percolating sets of [n]^d (d-neighbour bootstrap percolation).

For d = 3..5 and n = 3..20 it simulates up to three initial sets, all of size n^(d-1), and
writes one row (d, n, construction, time, size) each to notes/sweep-results.csv:

  canonical  A  = union_{i=1..d} V_{i n}                (Theorem 1 of Przykucki-Shelton)
  shifted    A' = union_{i=1..d} V_{i n - floor(n/2)}   (the paper's empirically better set;
                                                         nothing is proved about it)
  recursive  n = 2^p only: the even/odd-subcube construction from the proof of the linear
             upper bound m_d(2^p) <= d 2^p (spec: refs/code-context.md).

V_k = {v in [n]^d : v_1 + ... + v_d = k}. For small n some layers of A' are empty (sum < d);
that is fine, A' is still {v : sum(v) = -floor(n/2) mod n}, which has exactly n^(d-1) elements.

recursive(n, d): split [n]^d into 2^d subcubes of side m = n/2, indexed by a in {0,1}^d.
Subcubes with even index sum ("even") each get a copy of the recursive set for side m;
"odd" subcubes start empty. Base case n = 2: the vertices with even (0-indexed)
coordinate sum, one of the two bipartition classes of the hypercube [2]^d; the other
class has all d of its neighbours in it, so it is infected in round 1. The spec leaves
open which parity to use at each level and whether coordinates are 0- or 1-indexed;
this uses even parity at every level with 0-indexed coordinates, and `parities` can
change it. With that choice the set is exactly {x : x_1 xor ... xor x_d = 0}
(0-indexed); preflight checks that, so the recursion is implemented correctly.

Why it is fast: an odd subcube touches an even one across exactly one facet per axis, so
if the even subcubes are infected by time T(m), its vertex with local coordinates
c = (c_1..c_d), where c_i = 0 is the face next to an even subcube, is infected by time
T(m) + 1 + sum(c). Hence T(2m) <= T(m) + 1 + d(m-1), T(2) = 1 (recursive_time_bound),
which is below the paper's d*n. The sweep asserts both bounds hold for every recursive row.

Before any sweep the tests in test_simulate.py (Phase-1 hand-verified values) run, plus
cross-checks of the constructions below against hand_verify.py; any failure aborts the
run before a CSV is written.

Run:  python3 sage/sweep.py [--dmin 3 --dmax 5 --nmin 3 --nmax 20 --out notes/sweep-results.csv]
"""

import argparse
import csv
from itertools import product
from pathlib import Path
import time

import numpy as np

import hand_verify as hv
import simulate as sim
import test_simulate

DEFAULT_OUT = Path(__file__).resolve().parent.parent / "notes" / "sweep-results.csv"


# ---------------------------------------------------------------- constructions
# Each returns a boolean array of shape (n,)*d; vertex v = (v_1..v_d) is index v - 1.

def coordinate_sums(n, d):
    """S[v - 1] = v_1 + ... + v_d."""
    S = np.zeros((n,) * d, dtype=np.int32)
    for axis in range(d):
        shape = [1] * d
        shape[axis] = n
        S += np.arange(1, n + 1, dtype=np.int32).reshape(shape)
    return S


def layer_union(n, d, shift):
    """union_{i=1..d} V_{i n - shift}, taken literally from the definition."""
    S = coordinate_sums(n, d)
    A = np.zeros((n,) * d, dtype=bool)
    for i in range(1, d + 1):
        A |= S == i * n - shift
    return A


def canonical(n, d):
    return layer_union(n, d, 0)


def shifted(n, d):
    return layer_union(n, d, n // 2)


def is_power_of_two(n):
    return n >= 2 and n & (n - 1) == 0


def recursive(n, d, parities=None):
    """Recursive even/odd-subcube set for n = 2^p (see module docstring).

    `parities` has one entry per recursion level, outermost split first and the base
    case last (default all 0): that level carries the sets in subcubes whose index sum
    (base case: whose coordinate sum) has that parity.
    """
    if not is_power_of_two(n):
        raise ValueError(f"recursive construction needs n = 2^p, got n={n}")
    if parities is None:
        parities = (0,) * (n.bit_length() - 1)
    parity, inner = parities[0], parities[1:]
    A = np.zeros((n,) * d, dtype=bool)
    if n == 2:
        for x in product((0, 1), repeat=d):
            A[x] = sum(x) % 2 == parity
        return A
    m = n // 2
    sub = recursive(m, d, inner)
    for a in product((0, 1), repeat=d):
        if sum(a) % 2 == parity:
            A[tuple(slice(m * ai, m * (ai + 1)) for ai in a)] = sub
    return A


def recursive_time_bound(n, d):
    """Upper bound on T(recursive(n, d)): T(2) = 1, T(2m) <= T(m) + 1 + d(m-1)."""
    bound = 1
    m = 2
    while m < n:
        bound += 1 + d * (m - 1)
        m *= 2
    return bound


CONSTRUCTIONS = [("canonical", canonical), ("shifted", shifted), ("recursive", recursive)]


# -------------------------------------------------------------------- preflight

def as_tuples(mask):
    return {tuple(int(c) + 1 for c in idx) for idx in np.argwhere(mask)}


def xor_set(n, d, c):
    """{x in {0..n-1}^d : x_1 xor ... xor x_d = c} (0-indexed coordinates)."""
    return np.bitwise_xor.reduce(np.indices((n,) * d), axis=0) == c


def check_constructions():
    # Literal union of layers == residue class of the coordinate sum mod n (why |A| = n^(d-1)).
    for d in (3, 4, 5):
        for n in range(2, 9 if d < 5 else 6):
            S = coordinate_sums(n, d)
            assert (canonical(n, d) == (S % n == 0)).all(), (n, d)
            assert (shifted(n, d) == ((S + n // 2) % n == 0)).all(), (n, d)
            assert canonical(n, d).sum() == shifted(n, d).sum() == n ** (d - 1), (n, d)

    # numpy masks == the tuple sets hand_verify.py builds straight from the definition of V_k.
    for d, nmax in ((3, 7), (4, 5)):
        for n in range(2, nmax + 1):
            assert as_tuples(canonical(n, d)) == hv.canonical_A(n, d), (n, d)
            literal = set().union(*(hv.V(i * n - n // 2, n, d) for i in range(1, d + 1)))
            assert as_tuples(shifted(n, d)) == literal, (n, d)

    # The recursion really is the xor set; a mixed-parity choice is the xor set for the matching c.
    for d in (2, 3, 4):
        for n in (2, 4, 8):
            assert (recursive(n, d) == xor_set(n, d, 0)).all(), (n, d)
            p = n.bit_length() - 1
            for c in range(n):
                parities = tuple((c >> (p - 1 - j)) & 1 for j in range(p))   # outermost level = top bit
                assert (recursive(n, d, parities) == xor_set(n, d, c)).all(), (n, d, c)
            assert recursive(n, d).sum() == n ** (d - 1)

    # simulate() on the actual swept sets agrees with the brute-force simulator, round by round.
    cases = [(canonical, 3, range(3, 7)), (shifted, 3, range(3, 7)), (recursive, 3, (4, 8)),
             (canonical, 4, (3, 4)), (shifted, 4, (3, 4)), (recursive, 4, (4,)),
             (canonical, 5, (3,)), (shifted, 5, (3,)), (recursive, 5, (4,))]
    for build, d, ns in cases:
        for n in ns:
            mask = build(n, d)
            ref_trace = []
            ref_set, ref_rounds = hv.percolate(as_tuples(mask), n, d, trace=ref_trace)
            trace = []
            state, rounds = sim.run(mask, n, d, trace=trace)
            assert as_tuples(state) == ref_set and rounds == ref_rounds and trace == ref_trace, \
                (build.__name__, n, d)


def preflight():
    print("preflight 1/2: simulate.py vs. Phase-1 hand-verified values", flush=True)
    test_simulate.run_all()
    print("preflight 2/2: constructions vs. hand_verify.py and structural identities", flush=True)
    check_constructions()
    print("preflight passed.\n", flush=True)


# ------------------------------------------------------------------------ sweep

def sweep(dmin, dmax, nmin, nmax, out):
    out.parent.mkdir(parents=True, exist_ok=True)
    start = time.time()
    with open(out, "w", newline="") as f:
        writer = csv.writer(f, lineterminator="\n")
        writer.writerow(["d", "n", "construction", "time", "size"])
        for d in range(dmin, dmax + 1):
            for n in range(nmin, nmax + 1):
                for name, build in CONSTRUCTIONS:
                    if name == "recursive" and not is_power_of_two(n):
                        continue
                    t0 = time.time()
                    A = build(n, d)
                    size = int(A.sum())
                    assert size == n ** (d - 1), f"{name}: |A| = {size} != n^(d-1) for n={n}, d={d}"
                    infected, T = sim.simulate(A, n, d)
                    if not infected:
                        raise RuntimeError(f"{name} set does not percolate for n={n}, d={d}")
                    if name == "recursive":
                        assert T <= recursive_time_bound(n, d) <= d * n, \
                            f"recursive T = {T} exceeds bound {recursive_time_bound(n, d)} (d*n = {d * n}) " \
                            f"for n={n}, d={d}: construction misread or bound misderived"
                    writer.writerow([d, n, name, T, size])
                    f.flush()
                    print(f"d={d} n={n:2d} {name:9s} T={T:5d} |A|={size:7d}  ({time.time() - t0:.2f}s)", flush=True)
    print(f"\nwrote {out}  ({time.time() - start:.0f}s total)")


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--dmin", type=int, default=3)
    parser.add_argument("--dmax", type=int, default=5)
    parser.add_argument("--nmin", type=int, default=3)
    parser.add_argument("--nmax", type=int, default=20)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()
    preflight()
    sweep(args.dmin, args.dmax, args.nmin, args.nmax, args.out)


if __name__ == "__main__":
    main()
