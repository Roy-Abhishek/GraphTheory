import Mathlib
import BootstrapPercolation.MainResult
import BootstrapPercolation.Lemma1Triangle
import BootstrapPercolation.Lemma2Cube

/-! # The headline family theorem

Assembles `notes/log.md`'s "Proof for every k" into a single statement: for every level
`k`, with `m = mOf k = 2^(k+1) - 2` and `n = 2m + 1 = 2^(k+2) - 3` (the notes' own `k` in
"n = 2^k - 3" is this file's `k + 2` - re-indexed here to match `Lemma1Triangle.mOf`/
`Lemma2Cube.m`/`Lemma2Cube.n`'s existing convention rather than introduce a second `k`),
`Aset k`:

1. percolates (`BootstrapPercolation.Lemma2Cube.Aset_percolates` - proved, no gaps);
2. has exactly `n²` cells (`Aset_card_eq_n_sq` below);
3. takes exactly `3 * m` rounds to percolate - `3 * m = 3 * (n - 1) / 2` - the upper half via
   `Aset_afterRounds_three_m` (proved, no gaps) and the lower half via
   `corner_sink_lower_bound` below.

**Two pieces are cited, not proved, in this file** - both are real mathematics worked out by
hand in `notes/log.md`, but neither has been formalised:

- `Aset_card_eq_n_sq`: a recursive counting argument (`notes/log.md`, "Count: `|H| = 3m²+3m+1`
  and `|P(m)| = ... = m(m+1)/6`; the six gadgets and `H` are pairwise disjoint; so
  `|Aₙ| = 4m²+4m+1 = n²`"). Formalising it needs a closed-form size for `Pmem (m k)` (not yet
  established - `Lemma1Triangle`/`Lemma1ClaimI-III` prove *properties* of `ell`, not the size of
  its zero-locus) plus a disjointness argument between `H` and the six triangular gadgets.
- `corner_sink_lower_bound`: needs Przykucki-Shelton's own Theorem 1 (`|Aₙ| = n²` is the
  *minimum* possible size of a percolating set at this threshold - an external citation, not
  re-derived anywhere in this repo) to run a perimeter-tightness argument forcing the real
  infection-time digraph to have every in-degree exactly `0` or exactly `3` and no two adjacent
  cells infected simultaneously; every maximal directed path then ends at a cube corner (the
  only degree-`3` cells), and since the centre is at Manhattan distance `3m` from every corner,
  `T ≥ 3m` (`notes/log.md`, "Lower bound, odd n"). This needs the *dynamic* process's own
  structure (round numbers, in/out-degree, acyclicity) - genuinely new infrastructure beyond the
  static witness `L` that the rest of this project is built on - and was deliberately left as an
  explicit, documented gap rather than attempted, given the two-month project timeline.

A quick computational sanity check (done in Python against the exact recursive definition of
`ell_m`, before writing any of this file) ruled out the one shortcut that would have avoided
`corner_sink_lower_bound` entirely: `L` is *not* 1-Lipschitz on the grid (adjacent cells can
differ by up to `m/2`), so there is no simple "`L` is a distance function" argument for the
lower bound - the structure-theorem route above is genuinely needed.
-/

namespace BootstrapPercolation.Lemma2Cube

open BootstrapPercolation
open BootstrapPercolation.Lemma1Triangle
open scoped Classical

variable (k : ℕ)

/-- **Minimum-size claim** (cited, not proved - see the module doc comment above and
`notes/log.md`'s "Count: `|H| = 3m²+3m+1` and `|P(m)| = ... = m(m+1)/6` ... `|Aₙ| = 4m²+4m+1 =
n²`"). -/
theorem Aset_card_eq_n_sq : (Aset k).card = (n k) ^ 2 := by
  sorry

/-- **Corner-sink lower bound** (cited, not proved - see the module doc comment above and
`notes/log.md`'s "Lower bound, odd n": "the center cell is at Manhattan distance `d(n−1)/2`
from every corner, so `T ≥ d(n−1)/2`"). Phrased via `afterRounds`, matching this project's
existing style (`afterRounds_sup_eq_univ` etc. in `MainResult.lean`) rather than introducing a
new `percolationTime` function: together with `Aset_afterRounds_three_m` (round `3m` suffices)
and monotonicity (`afterRounds_subset_succ`), this pins the exact minimum round down to `3m`. -/
theorem corner_sink_lower_bound : afterRounds (Aset k) (3 * m k - 1) ≠ Finset.univ := by
  sorry

/-- **Headline family theorem.** For every `k`, with `m = mOf k` and `n = 2m + 1 = 2^(k+2) - 3`:
`Aset k` percolates, has exactly `n²` cells, and percolates in exactly `3m = 3(n-1)/2` rounds
(round `3m` suffices, round `3m - 1` does not). Matches `notes/log.md`'s "**Theorem.** For
n = 2^k − 3 (k ≥ 3), Aₙ percolates in [n]³, |Aₙ| = n², and T(Aₙ) = 3(n−1)/2", modulo the `k`
re-indexing noted above. -/
theorem headline_family_theorem :
    Percolates (Aset k) ∧
    (Aset k).card = (n k) ^ 2 ∧
    afterRounds (Aset k) (3 * m k) = Finset.univ ∧
    afterRounds (Aset k) (3 * m k - 1) ≠ Finset.univ :=
  ⟨Aset_percolates k, Aset_card_eq_n_sq k, Aset_afterRounds_three_m k, corner_sink_lower_bound k⟩

end BootstrapPercolation.Lemma2Cube
