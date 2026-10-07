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
def ell : ℕ → ℕ × ℕ → ℕ
  | m, (a, b) =>
      if m < 2 then
        0
      else
        let m₀ := m / 2 - 1
        if a % 2 = 0 ∧ b % 2 = 0 then
          0
        else if a % 2 = 1 then
          if b % 2 = 1 then
            2 * ell m₀ (a / 2, b / 2)
          else
            1 + min (2 * ell m₀ (a / 2, b / 2 - 1)) (2 * ell m₀ (a / 2, b / 2))
        else
          1 + min (2 * ell m₀ (a / 2 - 1, b / 2)) (2 * ell m₀ (a / 2, b / 2))
termination_by m p => m
decreasing_by all_goals omega

-- Sanity check against the hand-worked base case in the notes:
-- Δ₂ = {(0,0), (0,1), (1,0)}, ℓ₂ = 0, 1, 1.
#eval ell 2 (0, 0)  -- expect 0
#eval ell 2 (0, 1)  -- expect 1
#eval ell 2 (1, 0)  -- expect 1
#eval ell 6 (1, 1)  -- expect 0 (odd-odd source cell: 2 * ell 2 (0,0))

/-! ## The m-values the lemma is actually about

Claims (i)/(ii)/(iii) in the notes are proved "by induction on j" for `m = 2^j - 2`
(`notes/log.md`, "Proof for every k": "Setting: m = 2^j − 2 (j ≥ 2)"), NOT for an
arbitrary even `m`. That restriction matters: `ell`'s recursion `m₀ = m / 2 - 1` only
stays within the family (and hence keeps `m₀` even, matching rule (e)/(o)/(x)'s own
assumption that `m` is even) when `m` itself is `2^j - 2` - a generic even `m` can land
on an odd `m₀` (e.g. `m = 4` gives `m₀ = 1`), where `ell`'s base-case value (always `0`
for `m < 2`) and `Pmem`'s base case (always `False`, see `Lemma1ClaimIII.lean`) disagree,
breaking claim (iii) outright. So the claims are stated for `mOf k`, not arbitrary `m`,
and proved by plain induction on `k` (not strong induction on `m`). -/

/-- `mOf k = 2^(k+1) - 2`: `mOf 0 = 0`, `mOf 1 = 2`, `mOf 2 = 6`, `mOf 3 = 14`, ... -
matches `m = 2^j - 2` in the notes with `j = k + 1`. -/
def mOf (k : ℕ) : ℕ := 2 ^ (k + 1) - 2

/-- `ell`'s own `m₀ = m / 2 - 1` sends `mOf (k+1)` to exactly `mOf k`, staying in the
family throughout - this is the fact that lets the claims induct cleanly on `k`. -/
theorem mOf_succ (k : ℕ) : mOf (k + 1) = 2 * mOf k + 2 := by
  have hk : (0 : ℕ) < 2 ^ k := by positivity
  have h2 : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  have h3 : (2 : ℕ) ^ (k + 1 + 1) = 2 ^ (k + 1) * 2 := pow_succ 2 (k + 1)
  simp only [mOf]
  omega

#eval mOf 0  -- expect 0
#eval mOf 1  -- expect 2
#eval mOf 2  -- expect 6
#eval mOf 3  -- expect 14

end BootstrapPercolation.Lemma1Triangle
