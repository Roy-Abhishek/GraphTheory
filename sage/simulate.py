"""numpy simulator for r-neighbour bootstrap percolation on [n]^d.

Same rules and conventions as sage/hand_verify.py (the brute-force ground truth):
  - vertex set {1..n}^d (1-indexed tuples going in); u ~ v iff they differ by 1 in
    exactly one coordinate;
  - synchronous r-neighbour rule A_t = A_{t-1} + {u : |N(u) & A_{t-1}| >= r}, default r = d;
  - time = number of rounds that infected at least one new vertex. For a percolating A
    this is T(A) = min{t : A_t = [n]^d}; it is 0 if A is already everything.
    For a non-percolating A it is just the round at which the process froze, NOT a
    percolation time, so only read `time` when `infected` is True.

The grid is a boolean array of shape (n,)*d. Each round, neighbour counts come from
2d shifted slices of the array (slicing, never np.roll, so nothing wraps around).
tests: sage/test_simulate.py
"""

import numpy as np


def _initial_state(initial_set, n, d):
    """Fresh boolean array of shape (n,)*d from either a boolean array or an iterable of d-tuples."""
    shape = (n,) * d
    if isinstance(initial_set, np.ndarray) and initial_set.dtype == bool:
        if initial_set.shape != shape:
            raise ValueError(f"boolean initial set has shape {initial_set.shape}, expected {shape}")
        return initial_set.copy()
    state = np.zeros(shape, dtype=bool)
    points = list(initial_set)
    if not points:
        return state
    pts = np.array(points, dtype=np.int64)
    if pts.ndim != 2 or pts.shape[1] != d:
        raise ValueError(f"initial set must be an iterable of {d}-tuples")
    if pts.min() < 1 or pts.max() > n:       # a 0 would silently wrap to index -1 below
        raise ValueError(f"initial set has a coordinate outside 1..{n}")
    state[tuple((pts - 1).T)] = True
    return state


def run(initial_set, n, d, r=None, trace=None):
    """Run r-neighbour bootstrap percolation (default r = d) from `initial_set` on [n]^d.

    `initial_set` is an iterable of d-tuples with coordinates in 1..n, or a boolean
    array of shape (n,)*d. Returns (final boolean array, rounds taken). If `trace` is
    a list, the number of infected vertices after each round is appended to it
    (so trace[t-1] = |A_t|; |A_0| is not included).
    """
    if n < 1 or d < 1:
        raise ValueError("need n >= 1 and d >= 1")
    if r is None:
        r = d
    state = _initial_state(initial_set, n, d)
    counts = np.zeros(state.shape, dtype=np.uint8)      # 2d <= 255 neighbours, so uint8 is safe

    # For each axis: the two overlapping halves of the grid, as views (they stay valid
    # because state and counts are only ever modified in place).
    # lo = coordinates 1..n-1 along the axis, hi = coordinates 2..n.
    # Cell lo[k] has hi[k] as its +1 neighbour; cell hi[k] has lo[k] as its -1 neighbour.
    pairs = []
    for axis in range(d):
        lo = [slice(None)] * d
        hi = [slice(None)] * d
        lo[axis] = slice(0, n - 1)
        hi[axis] = slice(1, n)
        lo, hi = tuple(lo), tuple(hi)
        pairs.append((counts[lo], counts[hi], state[lo], state[hi]))

    rounds = 0
    while True:
        counts.fill(0)
        for counts_lo, counts_hi, state_lo, state_hi in pairs:
            np.add(counts_lo, state_hi, out=counts_lo)
            np.add(counts_hi, state_lo, out=counts_hi)
        newly = (counts >= r) & ~state       # decided from the old state only: synchronous
        if not newly.any():
            return state, rounds
        state |= newly
        rounds += 1
        if trace is not None:
            trace.append(int(state.sum()))


def simulate(initial_set, n, d, r=None):
    """-> (infected, time): did `initial_set` infect all of [n]^d, and after how many rounds."""
    state, rounds = run(initial_set, n, d, r)
    return bool(state.all()), rounds
