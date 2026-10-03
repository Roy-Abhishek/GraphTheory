"""Brute-force ground truth for d-neighbour bootstrap percolation on [n]^d.

Deliberately simple and unoptimized: the grid is a set of tuples, every round
rescans every vertex. Everything else in the project gets checked against this.

Conventions (match refs/code-context.md):
  - [n]^d has vertex set {1..n}^d; u ~ v iff they differ by 1 in exactly one coordinate.
  - r-neighbour rule: A_t = A_{t-1} + {u : |N(u) & A_{t-1}| >= r}, updated SYNCHRONOUSLY
    (every new infection in round t is decided from A_{t-1} only).
  - "d-neighbour" means r = d. Corners of [n]^d have exactly d neighbours, so a corner
    needs ALL of its neighbours infected before it can be infected.
  - Rounds taken = number of rounds that infected at least one new vertex. For a
    percolating A this is T(A) = min{t : A_t = [n]^d}; T = 0 if A is already everything.

Run:  python3 sage/hand_verify.py
"""

from functools import lru_cache
from itertools import combinations, product
import time


# ---------------------------------------------------------------- simulator

@lru_cache(maxsize=None)
def build_grid(n, d):
    """Return (vertices, nbrs): the vertex list of [n]^d and a dict vertex -> neighbour list."""
    vertices = list(product(range(1, n + 1), repeat=d))
    nbrs = {}
    for v in vertices:
        nbrs[v] = []
        for i in range(d):
            for delta in (-1, 1):
                w = v[:i] + (v[i] + delta,) + v[i + 1:]
                if 1 <= w[i] <= n:
                    nbrs[v].append(w)
    return vertices, nbrs


def percolate(A, n, d, r=None, trace=None):
    """Run r-neighbour bootstrap percolation from A on [n]^d (default r = d).

    Returns (final_infected_set, rounds_taken). If `trace` is a list, the number of
    vertices infected after each round is appended to it.
    """
    if r is None:
        r = d
    vertices, nbrs = build_grid(n, d)
    infected = set(A)
    rounds = 0
    while True:
        newly = set()
        for v in vertices:
            if v in infected:
                continue
            if sum(1 for w in nbrs[v] if w in infected) >= r:
                newly.add(v)
        if not newly:
            return infected, rounds
        infected |= newly          # applied only after the full scan -> synchronous
        rounds += 1
        if trace is not None:
            trace.append(len(infected))


# ------------------------------------------------------ canonical set A_d

def V(k, n, d):
    """V_k = {v in [n]^d : v_1 + ... + v_d = k}, built by filtering the whole grid."""
    return {v for v in product(range(1, n + 1), repeat=d) if sum(v) == k}


def canonical_A(n, d):
    """A = union over i = 1..d of V_{i*n}  (Theorem 1 of Przykucki-Shelton)."""
    A = set()
    for i in range(1, d + 1):
        A |= V(i * n, n, d)
    return A


def check_canonical(n, d):
    A = canonical_A(n, d)
    layer_sizes = [len(V(i * n, n, d)) for i in range(1, d + 1)]
    assert len(A) == n ** (d - 1), (n, d, len(A))
    trace = []
    infected, T = percolate(A, n, d, trace=trace)
    assert infected == set(product(range(1, n + 1), repeat=d)), f"A does not percolate for n={n}, d={d}"
    print(f"d={d} n={n}: |V_in| = {layer_sizes}, |A| = {len(A)} = n^(d-1); "
          f"A percolates, T(A) = {T}")
    print(f"        |A_t| for t=0..{T}: {[len(A)] + trace}  (total {n ** d})")
    return T


# --------------------------------------------- is n^(d-1) really the minimum?
#
# Argument (a hypothesis to try to break; the brute force below is the check).
# Let S be infected, e(S) = number of grid edges inside S, and
#     P(S) = 2d|S| - 2e(S)
# = number of (vertex of S, axis direction) pairs whose neighbour is NOT in S, where
# neighbours outside the grid count as "not in S". Infecting a vertex with a >= d
# infected grid neighbours changes P by 2d - 2a <= 0, so P never increases. At the end
# S = [n]^d and P = 2d * n^(d-1) (one boundary face per vertex on each of the 2d facets).
# At the start P(A) <= 2d|A|. Hence 2d|A| >= 2d n^(d-1), i.e. |A| >= n^(d-1).
#
# Brute force on the tiny case n = 3, d = 3 (27 vertices, bound n^(d-1) = 9):
# percolation is monotone in A (more infected -> more infected), so a percolating
# set of size k < 8 could be padded with arbitrary vertices to a percolating set of
# size exactly 8. So it suffices to test every 8-subset. As a positive control the
# same search must find a percolating 9-set (otherwise the search proves nothing).

def percolating_subsets(n, d, size, stop_at_first=False):
    """Count (or find the first of) the `size`-subsets of [n]^d that percolate."""
    vertices, _ = build_grid(n, d)
    everything = set(vertices)
    count = 0
    first = None
    for A in combinations(vertices, size):
        infected, _ = percolate(A, n, d)
        if infected == everything:
            count += 1
            if first is None:
                first = A
            if stop_at_first:
                break
    return count, first


def check_lower_bound(n, d):
    bound = n ** (d - 1)
    total = sum(1 for _ in combinations(range(n ** d), bound - 1))
    print(f"\nLower-bound check, n={n} d={d}: testing all {total} subsets of size {bound - 1} ...")
    t0 = time.time()
    count, _ = percolating_subsets(n, d, bound - 1)
    print(f"  size {bound - 1}: {count} percolating sets ({time.time() - t0:.0f}s)")
    assert count == 0, "a set smaller than n^(d-1) percolates!"
    count, first = percolating_subsets(n, d, bound, stop_at_first=True)
    print(f"  size {bound} (positive control): first percolating set found = {first}")
    assert count == 1, "search is vacuous: no percolating set of size n^(d-1) found"


# ------------------------------------------- calibration against known values
#
# Independent checks of the simulator against published exact values
# (Theorem 2: m_1(n) and m_2(n) = n - 1), using the same brute force.

def min_time_over_optimal_sets(n, d):
    """m_d(n) by brute force: min T(A) over percolating A with |A| = n^(d-1)."""
    vertices, _ = build_grid(n, d)
    everything = set(vertices)
    best = None
    for A in combinations(vertices, n ** (d - 1)):
        infected, T = percolate(A, n, d)
        if infected == everything and (best is None or T < best):
            best = T
    return best


def calibrate():
    print("\nCalibration (brute-force m_d(n) vs. closed forms):")
    for n in range(2, 8):
        print(f"  d=1 n={n}: m = {min_time_over_optimal_sets(n, 1)}  "
              f"(floor(n/2) = {n // 2}, ceil(n/2) = {-(-n // 2)})")
    for n in range(2, 6):
        m = min_time_over_optimal_sets(n, 2)
        print(f"  d=2 n={n}: m = {m}  (n-1 = {n - 1})")
        assert m == n - 1


if __name__ == "__main__":
    for n in (3, 4):
        check_canonical(n, 3)
    check_lower_bound(3, 3)
    calibrate()
    print("\nAll assertions passed.")
