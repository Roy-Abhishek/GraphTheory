"""Tests for sage/gadget.py: the explicit minimum percolating sets of [n]^3 with T = 3(n-1)/2, n = 2^k - 3.

  - the closed form of the face gadget equals the recursive definition (m = 2^j - 2 up to 510) and |P(m)| = m(m+1)/6;
  - the construction has n^2 cells, no two adjacent, and percolates in exactly 3(n-1)/2 rounds, checked with three
    independent simulators (minperc, simulate.py, and the Phase-1 pure-Python hand_verify) for the sizes each can do;
  - exact.c's unique face-only completion of the hexagon equals the construction (n = 5, 13, 29), and finds
    none for the other odd n up to 21;
  - the n = 13 triple family: the D3d-symmetric members and a sample of recombined ones are valid;
  - the steps of the proof in notes/log.md: the 2D triangle process (all cells infected, label <= m - a - b, odd-odd cells
    = twice the labels of the m0 triangle, mixed-parity cells = 1 + min of their odd-odd neighbours) up to m = 1022, and
    the local condition for the whole labeling of the cube (0 exactly on the set, every other cell has >= 3 earlier
    neighbours) up to n = 253.

Run:  python3 sage/test_gadget.py        (about 20 s)
"""

import random

import numpy as np

import gadget as g
import hand_verify as hv
import hexagon as hx
import minperc as mp
import simulate as sim


def independent(mask):
    """No two adjacent cells are both in the set (necessary for a minimum percolating set)."""
    for axis in range(3):
        lo, hi = [slice(None)] * 3, [slice(None)] * 3
        lo[axis], hi[axis] = slice(0, -1), slice(1, None)
        if (mask[tuple(lo)] & mask[tuple(hi)]).any():
            return False
    return True


def test_closed_form_and_count():
    for j in range(1, 10):
        m = 2 ** j - 2
        recursive = g.positions(m)
        closed = {(a, b) for a in range(m) for b in range(m - a) if g.in_gadget(m, a, b)}
        assert recursive == closed, m
        assert len(recursive) * 6 == m * (m + 1), m                       # exactly the number of fixers that n^2 needs
        assert all(a + b <= m - 2 for a, b in recursive), m
    assert g.valid_m(0) and g.valid_m(2) and not g.valid_m(4) and not g.valid_m(8) and not g.valid_m(10)
    print("  ok  closed form = recursion, |P(m)| = m(m+1)/6 for m = 2, 6, ..., 510", flush=True)


def test_construction_percolates_in_3m_rounds():
    for m in (2, 6, 14, 30, 62):
        n = 2 * m + 1
        mask = g.build(m)
        assert int(mask.sum()) == n * n and independent(mask)
        assert sim.simulate(mask, n, 3) == (True, 3 * m), n                  # simulate.py
        assert mp.percolates(mask) == (True, 3 * m), n                        # minperc.py
        if n <= 61:
            assert mp.exact_structure(mask)[0], n
        if n <= 29:                                                           # brute-force simulator of Phase 1
            cells = {tuple(int(c) + 1 for c in idx) for idx in np.argwhere(mask)}
            infected, T = hv.percolate(cells, n, 3)
            assert len(infected) == n ** 3 and T == 3 * m, n
    print("  ok  hexagon + P(m): n^2 cells, independent, percolates in exactly 3m rounds (n = 5 ... 125)", flush=True)


def test_solver_finds_exactly_the_construction():
    for n in (5, 13, 29):
        status, found, _ = hx.find(n, face=True, count=5, seconds=300)
        assert (status, found) == ("SAT", 1), (n, status, found)              # a unique face-only completion
        status, mask, _ = hx.find(n, face=True, seconds=300)
        assert mask is not None and (mask == g.build((n - 1) // 2)).all(), n
    for n in (3, 7, 9, 11, 13 + 2, 17, 19, 21):
        status, mask, _ = hx.find(n, face=True, seconds=300)
        assert status == "UNSAT" and mask is None, (n, status)
    print("  ok  exact.c: the face-only hexagon completion is unique and equals the construction at n = 5, 13, 29; "
          "none at n = 3, 7, 9, 11, 15, 17, 19, 21", flush=True)


def test_n13_family():
    assert len(g.TRIPLES13) == 84
    for t in g.TRIPLES13:
        mask = g.build13([t] * 6)
        assert g.valid13(mask) and mp.is_invariant(mask, "D3d"), t
    assert (g.build13([(0, 0, 0)] * 6) == g.build(6)).all()                   # the (0, 0, 0) member is the face-only one
    rng = random.Random(1)
    for _ in range(300):
        assert g.valid13(g.build13([rng.choice(g.TRIPLES13) for _ in range(6)]))
    print("  ok  n = 13: all 84 symmetric triple members valid; 300 random independent six-tuples valid", flush=True)


def test_triangle_lemma():
    """Lemma 1 of the proof: the 2D process on the face triangle, checked against the recursive description."""
    prev_L, prev_m = None, None
    for j in range(2, 11):
        m = 2 ** j - 2
        L = g.triangle_labels(m)
        a, b = np.indices(L.shape)
        tri = a + b <= m - 1
        assert (L[tri] >= 0).all(), m                                            # every triangle cell gets infected
        assert (L[tri] <= (m - a - b)[tri]).all(), m                             # never slower than the hexagon wave
        assert int(L[tri].max()) == m // 2, m
        if prev_L is not None:                                                   # odd-odd cells: 2 x the m0 labels
            m0 = prev_m
            for i in range(m0 + 1):
                for jj in range(m0 + 1 - i):
                    assert L[2 * i + 1, 2 * jj + 1] == 2 * prev_L[i, jj], (m, i, jj)
        for x in range(m):                                                       # mixed parity: 1 + min(odd-odd neighbours)
            for y in range(m - x):
                if (x + y) % 2:
                    nbrs = [(x - 1, y), (x + 1, y)] if x % 2 == 0 else [(x, y - 1), (x, y + 1)]
                    assert L[x, y] == 1 + min(L[c] for c in nbrs if min(c) >= 0), (m, x, y)
        prev_L, prev_m = L, m
    for m in (2, 6, 14, 30, 62):                                                 # same labels as the 3D simulation on the face
        T = mp.infection_times(g.build(m))[0]
        L = g.triangle_labels(m)
        assert all(int(T[g.to_global(g.APEX_FRAMES[0], (0, x, y), m)]) == L[x, y] for x in range(m) for y in range(m - x)), m
    print("  ok  2D triangle lemma: infected, label <= m-a-b, odd-odd = 2 x m0 labels, mixed = 1 + min (m = 2 ... 1022)", flush=True)


def test_local_condition():
    """Lemma 2 of the proof, checked on the actual arrays (no simulation): the labeling certifies T <= 3m."""
    for m in (2, 6, 14, 30, 62, 126):
        assert g.check_local_condition(m) == 3 * m
    # the check is not vacuous: a gadget with one cell missing leaves triangle cells that are never infected
    for m in (6, 14):
        damaged = g.triangle_labels(m, gadget=g.positions(m) - {(0, 0)})
        a, b = np.indices(damaged.shape)
        assert (damaged[a + b <= m - 1] < 0).any()
    print("  ok  local condition (>= 3 earlier neighbours, L = 0 exactly on the set, max L = 3m) for n = 5 ... 253; "
          "a damaged gadget fails", flush=True)


def run_all():
    test_closed_form_and_count()
    test_construction_percolates_in_3m_rounds()
    test_solver_finds_exactly_the_construction()
    test_n13_family()
    test_triangle_lemma()
    test_local_condition()


if __name__ == "__main__":
    run_all()
    print("gadget.py: the explicit sets are valid minimum percolating sets with T = 3(n-1)/2.")
