import Mathlib
import BootstrapPercolation.Lemma1Triangle

/-! # Lemma 1, claim (iii)

From `notes/log.md` (the `P(m)` definition at line 166-167, and claim (iii) in "Lemma 1 (one
triangle, in 2D)"): `ell m (a, b) = 0` exactly on `P(m)`, restricted to `Δ_m` (`a + b < m`),
for `m = mOf k` - see `Lemma1Triangle.lean`'s "The m-values the lemma is actually about"
for why (a generic even `m`'s `m₀` can be odd, where `ell`'s and `Pmem`'s base cases
disagree: `ell`'s is `0`, `Pmem`'s is `False`, and `0 = 0 ↔ False` is simply false).

Unlike claim (i), this one stays strict (`a + b < mOf k`, i.e. `Δ_m` only, not `Hyp_m`):
`P(m)` itself is only defined on `Δ_m` in the notes, and indeed `ell` is identically `0`
on `Hyp_m` too (every `Hyp_m` cell has `a + b` even, since `m` is even, so it's always
even-even or odd-odd, never mixed) - which is `0 = 0 ↔ False`, i.e. false, exactly as for
`ell`/`Pmem`'s disagreeing base cases above. So `Pmem` deliberately does *not* try to
characterize `Hyp_m`, and this claim cannot be relaxed to `≤` the way claim (i) was. The
odd-odd branch below still only ever needs the strict bound at the smaller level (checked
by hand: `a + b < mOf (k+1)` gives `i + j < mOf k` strictly, no boundary case), so no
`Hyp`-level fact about `Pmem` is ever needed. -/

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

theorem ell_eq_zero_iff :
    ∀ k a b : ℕ, a + b < mOf k → (ell (mOf k) (a, b) = 0 ↔ Pmem (mOf k) (a, b)) := by
  intro k
  induction k with
  | zero =>
      intro a b hab
      exfalso
      have hm0 : mOf 0 = 0 := by norm_num [mOf]
      omega
  | succ k ih =>
      intro a b hab
      have hsucc : mOf (k + 1) = 2 * mOf k + 2 := mOf_succ k
      have hm0eq : mOf (k + 1) / 2 - 1 = mOf k := by omega
      rw [ell, Pmem]
      dsimp only
      rw [hm0eq]
      split_ifs with hm2 he hao hoo
      · simp
      · simp
      · -- a, b both odd
        have key := ih (a / 2) (b / 2) (by omega)
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
