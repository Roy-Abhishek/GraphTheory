import Mathlib
import BootstrapPercolation.Lemma1Triangle

/-! # Lemma 1, claim (i)

From `notes/log.md`, "Lemma 1 (one triangle, in 2D)", claim (i): on `Δ_m`, `ell m (a, b)
≤ m - a - b`. Stated here for `a + b ≤ mOf k` (`Δ_m ∪ Hyp_m` together, not just `Δ_m`
strictly) and for `m = mOf k` rather than an arbitrary `m` - see `Lemma1Triangle.lean`'s
"The m-values the lemma is actually about" for why the `mOf` restriction is needed.

The `≤` (rather than strict `<`) is needed too: a mixed-parity cell's rule-(x) neighbours
`(a/2, b/2 - 1)` and `(a/2, b/2)` (or the symmetric pair) can land exactly on `Hyp_{m₀}`
of the smaller triangle (index sum `= mOf k` exactly, not `< mOf k`) even when `(a, b)`
itself is strictly inside `Δ_{mOf (k+1)}`, so the induction hypothesis needs to cover that
boundary. (Unlike claim (iii), which stays strict - see that file's comment.) -/

namespace BootstrapPercolation.Lemma1Triangle

theorem ell_le_remaining :
    ∀ k a b : ℕ, a + b ≤ mOf k → ell (mOf k) (a, b) ≤ mOf k - a - b := by
  intro k
  induction k with
  | zero =>
      intro a b hab
      have hm0 : mOf 0 = 0 := by norm_num [mOf]
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha
      subst hb
      rw [hm0]
      simp [ell]
  | succ k ih =>
      intro a b hab
      have hsucc : mOf (k + 1) = 2 * mOf k + 2 := mOf_succ k
      have hm0eq : mOf (k + 1) / 2 - 1 = mOf k := by omega
      rw [ell]
      dsimp only
      rw [hm0eq]
      split_ifs with hm2 he hao hoo
      · omega
      · omega
      · -- a, b both odd
        have key := ih (a / 2) (b / 2) (by omega)
        omega
      · -- a odd, b even
        have key1 := ih (a / 2) (b / 2 - 1) (by omega)
        have key2 := ih (a / 2) (b / 2) (by omega)
        omega
      · -- a even, b odd
        have key1 := ih (a / 2 - 1) (b / 2) (by omega)
        have key2 := ih (a / 2) (b / 2) (by omega)
        omega

end BootstrapPercolation.Lemma1Triangle
