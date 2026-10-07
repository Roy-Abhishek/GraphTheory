import Mathlib
import BootstrapPercolation.Lemma1Triangle

/-! # Lemma 1, claim (ii)

From `notes/log.md`: on `Δ_m`, every cell with `ell m (a, b) > 0` has at least 3 of its
(existing, i.e. nonnegative-coordinate) in-plane neighbours `(a±1,b)`, `(a,b±1)` with
strictly smaller `ell m` value.

Status: statement only, `sorry`'d for now. The hand proof splits into: a *mixed-parity*
cell, where the two even-even neighbours are always 0 and the third comes from whichever
side attains the `min` in rule (x); and an *odd-odd* cell `(2i+1,2j+1)`, which needs the
harder correspondence from the notes - 3 smaller neighbours of `(i,j)` at level `m₀` map to
3 *different* smaller neighbours of `(a,b)` at level `m`, via the midpoint cells. Neither
case is filled in here yet; this is next after claims (i) and (iii). -/

namespace BootstrapPercolation.Lemma1Triangle

/-- The (up to 4) candidate in-plane neighbours of `(a, b)` with nonnegative coordinates.
`ell` itself relies on Nat truncated subtraction silently duplicating `(a,b)`'s own
row/column when `a = 0` or `b = 0` (harmless there, since it's folded into a `min`);
`neighbors` instead filters those degenerate duplicates out explicitly, since here we need
the actual count of *distinct* existing neighbours. -/
def neighbors (a b : ℕ) : Finset (ℕ × ℕ) :=
  (if a ≥ 1 then {((a - 1, b) : ℕ × ℕ)} else ∅) ∪ {(a + 1, b)} ∪
  (if b ≥ 1 then {((a, b - 1) : ℕ × ℕ)} else ∅) ∪ {(a, b + 1)}

/-- Claim (ii). -/
theorem three_smaller_neighbours :
    ∀ m a b : ℕ, a + b < m → 0 < ell m (a, b) →
      3 ≤ (neighbors a b |>.filter (fun v => ell m v < ell m (a, b))).card := by
  sorry

end BootstrapPercolation.Lemma1Triangle
