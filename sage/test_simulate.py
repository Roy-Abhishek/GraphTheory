"""Tests for sage/simulate.py. Plain asserts, so a failure raises loudly.

Run:  python3 sage/test_simulate.py          (a few seconds)
      python3 sage/test_simulate.py --slow   (also the exhaustive [3]^3 search, minutes)

What is checked, in order:
  1. The exact values hand-verified in Phase 1 (notes/log.md), hard-coded below.
  2. Brute-force calibration values m_1(n), m_2(n) from Phase 1.
  3. Differential test: numpy simulate.py vs. the pure-Python hand_verify.percolate on
     random and structured sets over many (n, d, r): same final set, same number of
     rounds, same |A_t| after every round.
  4. Edge cases and input validation.
"""

from itertools import combinations, product
import random
import sys

import numpy as np

import hand_verify as hv
import simulate as sim


# ------------------------------------------------ 1. Phase-1 hand-verified values

# (n, d) -> (|V_n|, |V_2n|, |V_3n|, T(A), [|A_t| for t = 0..T])   from notes/log.md
HAND_VERIFIED_CANONICAL = {
    (3, 3): ([1, 7, 1], 3, [9, 15, 21, 27]),
    (4, 3): ([3, 12, 1], 6, [16, 30, 34, 40, 49, 61, 64]),
}

# The percolating 9-set that the Phase-1 search found first in [3]^3 (positive control).
PHASE1_PERCOLATING_9_SET = ((1, 1, 1), (1, 1, 3), (1, 2, 2), (1, 3, 1), (2, 2, 3),
                            (2, 3, 2), (3, 1, 1), (3, 1, 3), (3, 3, 3))


def test_hand_verified_values():
    for (n, d), (layer_sizes, T, sizes) in HAND_VERIFIED_CANONICAL.items():
        A = hv.canonical_A(n, d)
        assert [len(hv.V(i * n, n, d)) for i in range(1, d + 1)] == layer_sizes
        assert len(A) == n ** (d - 1) == sizes[0]

        infected, time = sim.simulate(A, n, d)
        assert infected, f"simulate(): canonical A does not percolate for n={n}, d={d}"
        assert time == T, f"simulate() gives T(A) = {time} for n={n}, d={d}; hand-verified value is {T}"

        trace = []
        sim.run(A, n, d, trace=trace)
        assert [len(A)] + trace == sizes, \
            f"simulate() gives |A_t| = {[len(A)] + trace} for n={n}, d={d}; hand-verified {sizes}"


def test_phase1_lower_bound_facts():
    # Positive control: Phase 1 found this 9-set percolating [3]^3.
    infected, _ = sim.simulate(PHASE1_PERCOLATING_9_SET, 3, 3)
    assert infected, "the percolating 9-set found in Phase 1 does not percolate under simulate()"
    # Phase 1: none of the C(27,8) 8-subsets percolate. Here a seeded random sample;
    # the exhaustive version is test_exhaustive_3_3_3 (--slow).
    rng = random.Random(8)
    vertices = list(product(range(1, 4), repeat=3))
    for _ in range(20000):
        A = rng.sample(vertices, 8)
        assert not sim.simulate(A, 3, 3)[0], f"an 8-set percolates [3]^3: {sorted(A)}"


# --------------------------------------------- 2. Phase-1 calibration (brute force)

# d -> {n: m_d(n)} by brute force over all sets of size n^(d-1)  (notes/log.md).
HAND_VERIFIED_M = {
    1: {2: 1, 3: 1, 4: 2, 5: 2, 6: 3, 7: 3},
    2: {2: 1, 3: 2, 4: 3, 5: 4},
}


def brute_force_m(n, d):
    best = None
    for A in combinations(product(range(1, n + 1), repeat=d), n ** (d - 1)):
        infected, T = sim.simulate(A, n, d)
        if infected and (best is None or T < best):
            best = T
    return best


def test_calibration():
    for d, table in HAND_VERIFIED_M.items():
        for n, expected in table.items():
            got = brute_force_m(n, d)
            assert got == expected, f"brute-force m_{d}({n}) = {got} with simulate(); Phase 1 found {expected}"


# ---------------------------------------- 3. differential test vs. hand_verify.py

def assert_same_as_ground_truth(A, n, d, r):
    ref_trace = []
    ref_set, ref_rounds = hv.percolate(A, n, d, r=r, trace=ref_trace)
    trace = []
    state, rounds = sim.run(A, n, d, r=r, trace=trace)
    final = {tuple(int(c) + 1 for c in idx) for idx in np.argwhere(state)}
    where = f"n={n}, d={d}, r={r}, |A|={len(A)}"
    assert final == ref_set, f"final infected sets differ ({where})"
    assert rounds == ref_rounds, f"rounds differ: numpy {rounds} vs brute force {ref_rounds} ({where})"
    assert trace == ref_trace, f"|A_t| traces differ ({where})"
    assert sim.simulate(A, n, d, r) == (len(ref_set) == n ** d, ref_rounds), where


def test_differential_vs_hand_verify():
    rng = random.Random(179)                    # fixed seed: failures are reproducible
    configs = [(2, 2), (3, 2), (6, 2), (2, 3), (3, 3), (4, 3), (5, 3), (3, 4), (4, 4), (2, 5), (3, 5)]
    for n, d in configs:
        vertices = list(product(range(1, n + 1), repeat=d))
        for r in range(1, 2 * d + 1):           # every threshold, not just r = d
            for _ in range(12):
                density = rng.choice([0.05, 0.1, 0.2, 0.35, 0.5])
                A = [v for v in vertices if rng.random() < density]
                assert_same_as_ground_truth(A, n, d, r)
    # structured sets that percolate and take many rounds
    for n, d in [(3, 3), (4, 3), (5, 3), (6, 3), (4, 4)]:
        canonical = hv.canonical_A(n, d)
        shifted = set().union(*(hv.V(i * n - n // 2, n, d) for i in range(1, d + 1)))
        for A in (canonical, shifted):
            for r in range(1, 2 * d + 1):
                assert_same_as_ground_truth(A, n, d, r)


# ------------------------------------------------- 4. edge cases and validation

def test_edge_cases():
    full_3x3 = list(product(range(1, 4), repeat=2))
    assert sim.simulate([], 3, 3) == (False, 0)               # nothing to spread
    assert sim.simulate(full_3x3, 3, 2) == (True, 0)          # already everything
    assert sim.simulate([(1, 1, 1)], 1, 3) == (True, 0)       # [1]^3 is a single vertex
    assert sim.simulate([], 1, 3) == (False, 0)
    assert sim.simulate([(1, 1)] * 3 + [(2, 2)], 2, 2) == (True, 1)   # duplicates are harmless; C4 antipodes

    # No wrap-around: on the path 1-2-3 a seed at 1 reaches 3 only via 2 (time 2, not 1).
    assert sim.simulate([(1,)], 3, 1) == (True, 2)
    assert sim.simulate([(1,)], 5, 1) == (True, 4)
    # Corner (1,1) of [3]^2 needs BOTH neighbours at r = d = 2; one neighbour is not enough.
    state, _ = sim.run([(1, 2)], 3, 2)
    assert not state[0, 0]
    state, _ = sim.run([(1, 2), (2, 1)], 3, 2)
    assert state[0, 0]
    # Path graph, r = 1: best single seed is the middle, time floor(n/2).
    for n in range(2, 12):
        assert sim.simulate([((n + 1) // 2,)], n, 1) == (True, n // 2)

    # Default r is d.
    A = hv.canonical_A(4, 3)
    assert sim.simulate(A, 4, 3) == sim.simulate(A, 4, 3, r=3)
    assert sim.simulate(A, 4, 3, r=2) != sim.simulate(A, 4, 3, r=3)

    # A boolean-array initial set behaves like the tuple list, and is not modified.
    arr = np.zeros((4, 4, 4), dtype=bool)
    for v in A:
        arr[tuple(c - 1 for c in v)] = True
    before = arr.copy()
    assert sim.simulate(arr, 4, 3) == sim.simulate(A, 4, 3)
    assert (arr == before).all()

    # trace holds |A_t| for t = 1..T.
    trace = []
    _, T = sim.run(A, 4, 3, trace=trace)
    assert len(trace) == T and trace[-1] == 4 ** 3 and trace == sorted(set(trace))


def test_input_validation():
    for bad in ([(0, 1, 1)], [(4, 1, 1)], [(1, 1)], [(1, 1, 1, 1)], [(-1, 1, 1)]):
        try:
            sim.simulate(bad, 3, 3)
        except ValueError:
            continue
        raise AssertionError(f"simulate({bad}, n=3, d=3) should raise ValueError")
    try:
        sim.simulate(np.zeros((3, 3), dtype=bool), 3, 3)
    except ValueError:
        pass
    else:
        raise AssertionError("wrong-shaped boolean array should raise ValueError")


# ------------------------------------------------------------- slow (optional)

def test_exhaustive_3_3_3():
    """Phase 1's exhaustive result, re-done with simulate(): no 8-subset of [3]^3 percolates."""
    vertices = list(product(range(1, 4), repeat=3))
    count = 0
    for A in combinations(vertices, 8):
        count += sim.simulate(A, 3, 3)[0]
    assert count == 0, f"{count} 8-subsets of [3]^3 percolate; Phase 1 found 0"


FAST_TESTS = [test_hand_verified_values, test_phase1_lower_bound_facts, test_calibration,
              test_differential_vs_hand_verify, test_edge_cases, test_input_validation]
SLOW_TESTS = [test_exhaustive_3_3_3]


def run_all(slow=False):
    for test in FAST_TESTS + (SLOW_TESTS if slow else []):
        test()
        print(f"  ok  {test.__name__}", flush=True)


if __name__ == "__main__":
    run_all(slow="--slow" in sys.argv)
    print("simulate.py reproduces all Phase-1 values.")
