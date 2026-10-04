"""Helpers for minimum-size percolating sets of boxes under r-neighbour bootstrap percolation.

Works on boolean arrays of any shape (a box a x b x c, or a cube [n]^3), unlike simulate.py,
which is cubes only. Cells are array indices, i.e. vertex v of [n]^d is index v - 1.

Structure of minimum percolating sets (r = d). Let A percolate the box and have the minimum
possible size, (surface area / 2) / d = (ab + bc + ca) / 3 for a 3-d box. The perimeter argument in
hand_verify.py is then tight, which forces
  - A is an independent set (no two adjacent cells),
  - every cell outside A has EXACTLY d earlier-infected neighbours when it is infected, and
  - no two adjacent cells are infected in the same round.
Orienting each grid edge from the earlier-infected to the later-infected end therefore gives an
acyclic orientation with every in-degree in {0, d}, whose sources are exactly A, and the
percolation time T(A) is the length of its longest directed path. Conversely any such
orientation has its sources as a percolating set. `exact_structure` checks this on a given
set; exhaustive_m3_3.py confirms it for every percolating 9-set of [3]^3.
"""

from itertools import permutations, product

import numpy as np


def _axis_halves(shape):
    """For each axis, the (lo, hi) slice tuples: cell lo[k] has hi[k] as its +1 neighbour."""
    d = len(shape)
    pairs = []
    for axis in range(d):
        lo = [slice(None)] * d
        hi = [slice(None)] * d
        lo[axis] = slice(0, shape[axis] - 1)
        hi[axis] = slice(1, shape[axis])
        pairs.append((tuple(lo), tuple(hi)))
    return pairs


def infection_times(mask, r=None):
    """(times, rounds): the round each cell is infected (0 = initial, -1 = never), synchronous
    r-neighbour rule on a box of any shape (default r = number of dimensions).

    rounds = number of rounds that infected at least one new cell, as in simulate.py.
    """
    state = np.array(mask, dtype=bool)               # private copy
    d = state.ndim
    if r is None:
        r = d
    times = np.where(state, 0, -1).astype(np.int32)
    counts = np.zeros(state.shape, dtype=np.uint8)
    pairs = _axis_halves(state.shape)
    rounds = 0
    while True:
        counts.fill(0)
        for lo, hi in pairs:
            counts[lo] += state[hi]
            counts[hi] += state[lo]
        newly = (counts >= r) & ~state
        if not newly.any():
            return times, rounds
        rounds += 1
        times[newly] = rounds
        state |= newly


def percolates(mask, r=None):
    """(does it percolate, rounds) for a boolean box."""
    times, rounds = infection_times(mask, r)
    return bool((times >= 0).all()), rounds


def neighbour_time_counts(times):
    """(earlier, equal): per cell, how many neighbours have a strictly smaller / an equal time."""
    earlier = np.zeros(times.shape, dtype=np.int32)
    equal = np.zeros(times.shape, dtype=np.int32)
    for lo, hi in _axis_halves(times.shape):
        a, b = times[lo], times[hi]                  # a[k] and b[k] are adjacent cells
        earlier[hi] += a < b                         # a is earlier than b: counts for b
        earlier[lo] += b < a
        equal[lo] += a == b
        equal[hi] += a == b
    return earlier, equal


def exact_structure(mask, r=None):
    """(ok, reason): does this percolating box have the tight structure described above?"""
    times, _ = infection_times(mask, r)
    d = times.ndim
    r = d if r is None else r
    if (times < 0).any():
        return False, "does not percolate"
    earlier, equal = neighbour_time_counts(times)
    if (equal > 0).any():
        return False, "two adjacent cells are infected in the same round"
    bad = (earlier != r) & (times > 0)
    if bad.any():
        return False, f"{int(bad.sum())} infected cells do not have exactly {r} earlier neighbours"
    if ((earlier != 0) & (times == 0)).any():
        return False, "two initial cells are adjacent"
    return True, "ok"


def longest_path(times):
    """Longest directed path (in edges) of the orientation by infection time; equals max(times)."""
    return int(times.max())


# --------------------------------------------------------------- cube symmetries

def cube_symmetries(d=3):
    """All 2^d * d! axis permutations with reflections, as functions on boolean arrays of a cube."""
    syms = []
    for perm in permutations(range(d)):
        for flips in product((False, True), repeat=d):
            def apply(a, perm=perm, flips=flips):
                b = np.transpose(a, perm)
                for axis, flip in enumerate(flips):
                    if flip:
                        b = np.flip(b, axis)
                return b
            syms.append(apply)
    return syms


_SYMS = {}


def canonical_form(mask):
    """Smallest (as bytes) image of a cube-shaped boolean array under the cube symmetry group.

    Two sets are equivalent under symmetry iff their canonical forms are equal.
    """
    d = mask.ndim
    if d not in _SYMS:
        _SYMS[d] = cube_symmetries(d)
    return min(np.ascontiguousarray(s(mask)).tobytes() for s in _SYMS[d])


def stabilizer_size(mask):
    """Number of cube symmetries that map the set to itself."""
    d = mask.ndim
    if d not in _SYMS:
        _SYMS[d] = cube_symmetries(d)
    return sum(bool((s(mask) == mask).all()) for s in _SYMS[d])


def line_counts(mask):
    """For a 3-d cube: per axis, how many axis-parallel lines contain 0, 1, 2, ... points."""
    out = []
    for axis in range(mask.ndim):
        per_line = mask.sum(axis=axis)
        out.append(np.bincount(per_line.ravel(), minlength=mask.shape[axis] + 1))
    return out


def is_latin(mask):
    """True iff every axis-parallel line contains exactly one point (the set is a Latin square)."""
    return all(((mask.sum(axis=axis)) == 1).all() for axis in range(mask.ndim))


# ----------------------------------------------------- symmetry-restricted search

# Generators of some subgroups of the cube group, as (axis permutation, reflected axes) pairs.
GROUPS = {
    "none": [],
    "inv": [((0, 1, 2), (1, 1, 1))],                                     # point reflection v -> n + 1 - v
    "C3": [((1, 2, 0), (0, 0, 0))],                                      # cyclic shift of the coordinates
    "S3": [((1, 0, 2), (0, 0, 0)), ((1, 2, 0), (0, 0, 0))],              # all coordinate permutations
    "D3d": [((1, 0, 2), (0, 0, 0)), ((1, 2, 0), (0, 0, 0)), ((0, 1, 2), (1, 1, 1))],   # S3 and the point reflection
}


def apply_symmetry(a, perm, flips):
    b = np.transpose(a, perm)
    for axis, flip in enumerate(flips):
        if flip:
            b = np.flip(b, axis)
    return b


def orbits(n, group):
    """Partition the cells of [n]^3 (flat indices, C order) into orbits of the named group (see GROUPS)."""
    idx = np.arange(n ** 3).reshape((n,) * 3)
    parent = list(range(n ** 3))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    for perm, flips in GROUPS[group]:
        image = apply_symmetry(idx, perm, flips).ravel()
        for k in range(n ** 3):
            parent[find(int(image[k]))] = find(k)
    out = {}
    for i in range(n ** 3):
        out.setdefault(find(i), []).append(i)
    return sorted(out.values())


def is_invariant(mask, group):
    """Is the boolean cube mapped to itself by every generator of the named group?"""
    return all((apply_symmetry(mask, perm, flips) == mask).all() for perm, flips in GROUPS[group])
