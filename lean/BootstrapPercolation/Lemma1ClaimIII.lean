import Mathlib
import BootstrapPercolation.Lemma1Triangle

/-! # Lemma 1, claim (iii)

From `notes/log.md` (the `P(m)` definition at line 166-167, and claim (iii) in "Lemma 1 (one
triangle, in 2D)"): `ell m (a, b) = 0` exactly on `P(m)`, restricted to `Δ_m` (`a + b < m`).

`Pmem` mirrors `P(0) = ∅`, `P(m) = {(2i,2j) : i+j ≤ m₀} ∪ {(2i+1,2j+1) : (i,j) ∈ P(m₀)}`
(`m₀ = m/2 - 1`), using the *same* case nesting as `ell` (m < 2; both even; a odd then
b odd/even; else) so the two unfold in lockstep under one `split_ifs`. -/

namespace BootstrapPercolation.Lemma1Triangle

def Pmem : ℕ → ℕ × ℕ → Prop
  | m, (a, b) =>
      if m < 2 then
        False
      else
        let m₀ := m / 2 - 1
        if a % 2 = 0 ∧ b % 2 = 0 then
          a / 2 + b / 2 ≤ m₀
        else if a % 2 = 1 then
          if b % 2 = 1 then
            Pmem m₀ (a / 2, b / 2)
          else
            False
        else
          False
termination_by m p => m
decreasing_by all_goals omega

theorem ell_eq_zero_iff : ∀ m a b : ℕ, a + b < m → (ell m (a, b) = 0 ↔ Pmem m (a, b)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro a b hab
    rw [ell, Pmem]
    dsimp only
    split_ifs with hm2 he hao hoo
    · simp
    · simp
    · -- a, b both odd
      have hm0 : m / 2 - 1 < m := by omega
      have key := ih (m / 2 - 1) hm0 (a / 2) (b / 2) (by omega)
      constructor
      · intro h
        exact key.mp (by omega)
      · intro h
        have := key.mpr h
        omega
    · -- a odd, b even: ell-value is 1 + min(...) ≠ 0, Pmem-value is False
      constructor
      · intro h; omega
      · intro h; exact h.elim
    · -- a even, b odd
      constructor
      · intro h; omega
      · intro h; exact h.elim

end BootstrapPercolation.Lemma1Triangle
