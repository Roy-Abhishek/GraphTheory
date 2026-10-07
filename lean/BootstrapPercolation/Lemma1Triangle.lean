import Mathlib

/-! # Lemma 1 (one triangle, in 2D)

From `notes/log.md`, "Lemma 1 (one triangle, in 2D)". Defines `ell m (a, b)` = ℓ_m(a, b)
by the recursion (e)/(o)/(x) on `m = 2 m₀ + 2`, from `ell m₀`. Only values on
`Δ_m ∪ Hyp_m = {(a, b) : a + b ≤ m}` are meaningful; this file is just the definition
and a couple of sanity checks against the hand-worked base case. Claims (i)/(ii)/(iii)
come next, once this compiles. -/

namespace BootstrapPercolation.Lemma1Triangle

/-- `ell m (a, b)` is ℓ_m(a, b). Base: `ell 0 _ = 0` (meaningful only at `(0,0)`, the
singleton `Hyp₀`). For `m ≥ 2`, with `m₀ = m / 2 - 1`:
(e) both coordinates even → `0`;
(o) both odd, `a = 2i+1`, `b = 2j+1` → `2 * ell m₀ (i, j)`;
(x) mixed parity → `1 + min` of the two odd-odd in-plane neighbours' values, computed via
`ell m₀`. Nat truncated subtraction makes the boundary case (where one neighbour would have
a negative coordinate) collapse to duplicating the other neighbour, matching "existing
neighbours" automatically. -/
def ell (m : ℕ) (p : ℕ × ℕ) : ℕ :=
  if m < 2 then 0
  else
    let m₀ := m / 2 - 1
    let a := p.1
    let b := p.2
    if a % 2 = 0 ∧ b % 2 = 0 then
      0
    else if a % 2 = 1 then
      if b % 2 = 1 then
        2 * ell m₀ (a / 2, b / 2)
      else
        1 + min (2 * ell m₀ (a / 2, b / 2 - 1)) (2 * ell m₀ (a / 2, b / 2))
    else
      1 + min (2 * ell m₀ (a / 2 - 1, b / 2)) (2 * ell m₀ (a / 2, b / 2))
termination_by m => m
decreasing_by all_goals omega

-- Sanity check against the hand-worked base case in the notes:
-- Δ₂ = {(0,0), (0,1), (1,0)}, ℓ₂ = 0, 1, 1.
#eval ell 2 (0, 0)  -- expect 0
#eval ell 2 (0, 1)  -- expect 1
#eval ell 2 (1, 0)  -- expect 1
#eval ell 6 (1, 1)  -- expect 0 (odd-odd source cell: 2 * ell 2 (0,0))

end BootstrapPercolation.Lemma1Triangle
