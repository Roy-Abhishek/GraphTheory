import Mathlib
import BootstrapPercolation.Basic

/-!
# `d`-neighbour bootstrap percolation on the grid `[n]^d`

Sets up `r = d` bootstrap percolation on the grid `Fin d → Fin n` (the
threshold studied throughout Przykucki-Shelton, "Smallest Percolating Sets
in Bootstrap Percolation on Grids", EJC 27(4) 2020, #P4.34), and proves the
**certificate lemma** from `notes/log.md` (2026-10-04, "Proof for every k"):
an explicit infection-time witness function on the grid certifies both that
a seed set percolates and a bound on how long it takes.

This is the one tool every upper bound in this project rests on. Lemma 1 and
Lemma 2's witness `L(u) = |Σ(u)|` off the six triangles / gadgets is a
certificate in exactly this sense, so `T(Aₙ) ≤ max L = 3m` for the explicit
family `Aₙ`, n = 2^k − 3, is a direct corollary once that witness is written
down (not yet formalised here - this file is the certificate lemma alone).

Classical logic is opened once so every `Finset.filter` below just
typechecks; we only ever reason about `step`, never evaluate it, so
decidability is not a real concern.
-/

open scoped Classical

namespace BootstrapPercolation

/-- A cell of the grid `[n]^d`: one coordinate in `Fin n` per axis. -/
abbrev Cell (d n : ℕ) := Fin d → Fin n

variable {d n : ℕ}

/-- Manhattan (ℓ¹) distance between two cells. -/
def mdist (u v : Cell d n) : ℕ :=
  ∑ i : Fin d, (((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ)).natAbs

/-- Two cells are grid-adjacent iff they differ by exactly one unit step. -/
def adjacent (u v : Cell d n) : Prop := mdist u v = 1

/-- `mdist` is symmetric. -/
lemma mdist_comm (u v : Cell d n) : mdist u v = mdist v u := by
  unfold mdist
  apply Finset.sum_congr rfl
  intro i _
  have h : ((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ)
      = -(((v i : ℕ) : ℤ) - ((u i : ℕ) : ℤ)) := by ring
  rw [h, Int.natAbs_neg]

/-- `adjacent` is symmetric. -/
lemma adjacent_symm {u v : Cell d n} (h : adjacent u v) : adjacent v u := by
  unfold adjacent at h ⊢
  rwa [mdist_comm u v] at h

/-- One synchronous round of `r = d` bootstrap percolation: an uninfected
cell joins the infected set once at least `d` of its neighbours are
infected. -/
noncomputable def step (A : Finset (Cell d n)) : Finset (Cell d n) :=
  A ∪ Finset.univ.filter
    (fun v => d ≤ (Finset.univ.filter (fun u => adjacent u v ∧ u ∈ A)).card)

/-- The process is extensive: nothing already infected is ever lost. -/
lemma subset_step (A : Finset (Cell d n)) : A ⊆ step A :=
  fun u hu => Finset.mem_union_left _ hu

/-- The infected set after `t` synchronous rounds. -/
noncomputable def afterRounds (A : Finset (Cell d n)) : ℕ → Finset (Cell d n)
  | 0 => A
  | (t + 1) => step (afterRounds A t)

/-- The process is monotone in time: more rounds only add cells. -/
lemma afterRounds_subset_succ (A : Finset (Cell d n)) (t : ℕ) :
    afterRounds A t ⊆ afterRounds A (t + 1) :=
  subset_step (afterRounds A t)

/-- `A` percolates if every cell is eventually infected. -/
def Percolates (A : Finset (Cell d n)) : Prop :=
  ∃ t, afterRounds A t = Finset.univ

/-- **Certificate lemma.** If `L` vanishes exactly on `A` and every cell with
`L u > 0` has at least `d` neighbours of strictly smaller `L`, then every
cell `u` with `L u ≤ t` is infected by round `t`. (`notes/log.md`: "induct on
`L(u)`, its `d` earlier neighbours are infected by round `L(u) − 1`".) -/
theorem certificate (A : Finset (Cell d n)) (L : Cell d n → ℕ)
    (hA : ∀ u, u ∈ A ↔ L u = 0)
    (hstep : ∀ u, L u ≠ 0 →
      d ≤ (Finset.univ.filter (fun v => adjacent u v ∧ L v < L u)).card) :
    ∀ t u, L u ≤ t → u ∈ afterRounds A t := by
  intro t
  induction t with
  | zero =>
      intro u hu
      exact (hA u).mpr (Nat.le_zero.mp hu)
  | succ t ih =>
      intro u hu
      rcases lt_or_ge (L u) (t + 1) with hlt | hge
      · exact afterRounds_subset_succ A t (ih u (Nat.lt_succ_iff.mp hlt))
      · have hLu : L u = t + 1 := le_antisymm hu hge
        have hcard := hstep u (by omega)
        show u ∈ step (afterRounds A t)
        apply Finset.mem_union_right
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ u, le_trans hcard (Finset.card_le_card ?_)⟩
        intro v hv
        rw [Finset.mem_filter] at hv ⊢
        have hvlt : L v < L u := hv.2.2
        exact ⟨hv.1, adjacent_symm hv.2.1, ih v (by omega)⟩

/-- Corollary: with a certificate `L`, every cell is infected by round
`L u` - no need to first pick a time `t`. -/
theorem infected_by (A : Finset (Cell d n)) (L : Cell d n → ℕ)
    (hA : ∀ u, u ∈ A ↔ L u = 0)
    (hstep : ∀ u, L u ≠ 0 →
      d ≤ (Finset.univ.filter (fun v => adjacent u v ∧ L v < L u)).card)
    (u : Cell d n) : u ∈ afterRounds A (L u) :=
  certificate A L hA hstep (L u) u le_rfl

/-- Corollary: a certificate on the whole grid makes `A` percolate, in at
most `sup L` rounds - `T(A) ≤ sup L`, matching `notes/log.md`'s
"So `T(A) ≤ max L`". -/
theorem afterRounds_sup_eq_univ (A : Finset (Cell d n)) (L : Cell d n → ℕ)
    (hA : ∀ u, u ∈ A ↔ L u = 0)
    (hstep : ∀ u, L u ≠ 0 →
      d ≤ (Finset.univ.filter (fun v => adjacent u v ∧ L v < L u)).card) :
    afterRounds A (Finset.univ.sup L) = Finset.univ :=
  Finset.eq_univ_of_forall fun u =>
    certificate A L hA hstep (Finset.univ.sup L) u (Finset.le_sup (Finset.mem_univ u))

theorem percolates_of_certificate (A : Finset (Cell d n)) (L : Cell d n → ℕ)
    (hA : ∀ u, u ∈ A ↔ L u = 0)
    (hstep : ∀ u, L u ≠ 0 →
      d ≤ (Finset.univ.filter (fun v => adjacent u v ∧ L v < L u)).card) :
    Percolates A :=
  ⟨Finset.univ.sup L, afterRounds_sup_eq_univ A L hA hstep⟩

end BootstrapPercolation
