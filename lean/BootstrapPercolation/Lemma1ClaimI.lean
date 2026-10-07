import Mathlib
import BootstrapPercolation.Lemma1Triangle

/-! # Lemma 1, claim (i)

From `notes/log.md`, "Lemma 1 (one triangle, in 2D)", claim (i): on `Δ_m` (`a + b < m`),
`ell m (a, b) ≤ m - a - b`. First attempt at the inductive proof, mirroring the recursive
case structure of `ell` itself via strong induction on `m`. -/

namespace BootstrapPercolation.Lemma1Triangle

theorem ell_le_remaining : ∀ m a b : ℕ, a + b < m → ell m (a, b) ≤ m - a - b := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro a b hab
    rw [ell]
    dsimp only
    split_ifs with hm2 he hao hoo
    · omega
    · omega
    · -- a, b both odd
      have hm0 : m / 2 - 1 < m := by omega
      have key := ih (m / 2 - 1) hm0 (a / 2) (b / 2) (by omega)
      omega
    · -- a odd, b even
      have hm0 : m / 2 - 1 < m := by omega
      have key1 := ih (m / 2 - 1) hm0 (a / 2) (b / 2 - 1) (by omega)
      have key2 := ih (m / 2 - 1) hm0 (a / 2) (b / 2) (by omega)
      omega
    · -- a even, b odd
      have hm0 : m / 2 - 1 < m := by omega
      have key1 := ih (m / 2 - 1) hm0 (a / 2 - 1) (b / 2) (by omega)
      have key2 := ih (m / 2 - 1) hm0 (a / 2) (b / 2) (by omega)
      omega

end BootstrapPercolation.Lemma1Triangle
