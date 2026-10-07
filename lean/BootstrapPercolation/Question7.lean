import Mathlib
import BootstrapPercolation.MainResult

/-! # Question 7 (Przykucki-Shelton, EJC 2020) — the general open conjecture

States the paper's own open question as an explicit Lean conjecture, kept deliberately
separate from `BootstrapPercolation.Lemma2Cube.headline_family_theorem` (the *proved* special
case this project resolves: `d = 3`, `n = 2^k - 3`). The point of this file is purely
bookkeeping for the write-up: one theorem the paper can cite as machine-checked (modulo its own
two documented gaps), and one conjecture, stated precisely, that remains open in general.

From `claude/context.md` (quoting the paper, via `Cell`/`Percolates`/`afterRounds` from
`MainResult.lean`, which already sets up exactly `r = d` bootstrap percolation on `[n]^d`):

- `T(A)`, the *percolation time* of a percolating set `A`: the number of rounds until every
  vertex is infected - `percolationTime` below.
- A *smallest* percolating set: one of minimum size among all percolating sets of `[n]^d`
  (the paper's own Theorem 1 - not re-derived in this repo - identifies this minimum size as
  exactly `n^(d-1)`, but that fact is not baked into the definition below, only into the
  "`∀ B, Percolates B → A.card ≤ B.card`" minimality clause, matching the paper's own definition
  rather than assuming its proved consequence).
- `m_d(n) := min{T(A) : A a smallest percolating set of [n]^d}` - `mdn` below.

> **Question 7.** Is `m_d(n) = o(n²)` for all `d ≥ 3`?

The authors state they "expect the answer to be positive." In plain terms: for *every* `n`, not
just the power-of-2 case the paper already handles, can a smallest percolating set of `[n]^d`
always be found that percolates in sub-quadratic time? `headline_family_theorem` answers this
affirmatively and *exactly* (`Θ(n)`, not merely `o(n²)`) for `d = 3` along the infinite family
`n = 2^k - 3` - a strictly stronger conclusion than the conjecture asks for, but only along one
family of `n`, not all of them, and only for `d = 3`, not all `d ≥ 3`. The general conjecture
below is what remains open.

Little-`o` is spelled out elementarily (an `ε`-`N` statement over `ℝ`) rather than via
`Mathlib`'s `Asymptotics.IsLittleO`, to keep this file readable without pulling in the filter
machinery - this is a bookkeeping statement, not something meant to be proved here. -/

namespace BootstrapPercolation

open scoped Classical

variable {d n : ℕ}

/-- The percolation time of a percolating set: the least round at which it has infected the
whole grid (well-defined - `sInf` of a nonempty set of `ℕ` - whenever `Percolates A` holds;
`sInf ∅ = 0` by Mathlib's convention otherwise, which is harmless here since `percolationTime`
is only ever used below under a `Percolates` hypothesis). -/
noncomputable def percolationTime (A : Finset (Cell d n)) : ℕ :=
  sInf {t | afterRounds A t = Finset.univ}

/-- A percolating set is smallest if no percolating set of `[n]^d` is strictly smaller - the
paper's own definition, not assuming its proved consequence (Theorem 1: this minimum size is
exactly `n^(d-1)`). -/
def IsSmallestPercolating (A : Finset (Cell d n)) : Prop :=
  Percolates A ∧ ∀ B : Finset (Cell d n), Percolates B → A.card ≤ B.card

/-- Przykucki-Shelton's `m_d(n)`: the minimum percolation time among the smallest percolating
sets of `[n]^d`. -/
noncomputable def mdn (d n : ℕ) : ℕ :=
  sInf {t | ∃ A : Finset (Cell d n), IsSmallestPercolating A ∧ percolationTime A = t}

/-- **Open Question 7** (Przykucki-Shelton, EJC 2020, end of §4): is `m_d(n) = o(n²)` for every
`d ≥ 3`? Stated here as an explicit conjecture - deliberately `sorry`'d, not attempted - so the
write-up can cite `headline_family_theorem` as the proved special case and this as the
precisely-stated general question it partially addresses. -/
theorem question_7 :
    ∀ d ≥ 3, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, (mdn d n : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
  sorry

end BootstrapPercolation
