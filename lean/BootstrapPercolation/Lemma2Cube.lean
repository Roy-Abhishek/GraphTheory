import Mathlib
import BootstrapPercolation.MainResult
import BootstrapPercolation.Lemma1Triangle
import BootstrapPercolation.Lemma1ClaimI
import BootstrapPercolation.Lemma1ClaimII
import BootstrapPercolation.Lemma1ClaimIII

/-! # Lemma 2 (the cube)

From `notes/log.md`: fix `m = 2^(k+1) - 2` (the family `Lemma1Triangle.mOf k`) and work on the
cube `[n]^3`, `n = 2m + 1`, in *centered* coordinates `coord u i = (u i : ℤ) - m ∈ [-m, m]`, so
`Σ(u) = coord u 0 + coord u 1 + coord u 2` is the signed "height". `H = {Σ = 0}` is the hexagonal
cross-section through the centre; `Tri` is the union of the six triangular corner faces (some
coordinate pinned to `±m`, with `Σ` strictly of the matching sign). Each piece of `Tri` carries
its own copy of `Δ_m` via `triCoord`, exactly as in `notes/log.md` ("for the face `u₁ = −m`:
`a = m−u₂, b = m−u₃`"), letting `ell`/`Pmem` from `Lemma1Triangle`/`Lemma1ClaimIII` be reused as
a black box instead of re-deriving the triangle's recursion in 3D.

`L` is the single witness function for the whole cube: `|Σ|` off `Tri`, `ell m (triCoord u)` on
`Tri`. `Aset` is the claimed minimal percolating set: `H` together with the zero-locus of `ell m`
(i.e. `Pmem m`, via `triCoord`) on each triangle. Lemma 2's three claims - `L = 0` exactly on
`Aset`, `L ≤ 3m` everywhere (with equality at the corners), and every positive-`L` cell has ≥3
in-cube neighbours of strictly smaller `L` - are stated below as the next proof targets (`sorry`
for now); together with `BootstrapPercolation.percolates_of_certificate`/`afterRounds_sup_eq_univ`
from `MainResult.lean` (specialised to `d = 3`, `A = Aset k`), they are exactly what the headline
theorem's upper bound `T(Aₙ) ≤ 3m` needs. -/

namespace BootstrapPercolation.Lemma2Cube

open BootstrapPercolation
open BootstrapPercolation.Lemma1Triangle
open scoped Classical

variable (k : ℕ)

/-- `m` in the notes' "Setting: `m = 2^j − 2`" - the level index `k` matches `Lemma1Triangle.mOf`. -/
def m : ℕ := mOf k

/-- The cube's side length, `n = 2m + 1`, so centered coordinates run over `[-m, m]`. -/
def n : ℕ := 2 * m k + 1

/-- `n` is always positive (`Fin (n k)` and `Cell 3 (n k)` are inhabited). -/
lemma n_pos : 0 < n k := by unfold n; omega

/-- A cell of the cube `[n]³`, reusing `BootstrapPercolation.Cell`'s indexing convention. -/
abbrev CubeCell := Cell 3 (n k)

/-- Shift a coordinate from `Fin n` (values `0, …, n−1`) to the centered range `[-m, m]`. -/
def coord (u : CubeCell k) (i : Fin 3) : ℤ := (u i : ℕ) - (m k : ℤ)

/-- `Σ(u) = u₁ + u₂ + u₃` in centered coordinates. -/
def Sigma (u : CubeCell k) : ℤ := coord k u 0 + coord k u 1 + coord k u 2

/-- `H`, the hexagonal cross-section `Σ = 0`. -/
def InH (u : CubeCell k) : Prop := Sigma k u = 0

/-- `Tri`, the union of the six triangular corner faces: some coordinate pinned to `-m` with
`Σ > 0`, or to `+m` with `Σ < 0` (`notes/log.md`: "`Tri = {u : some uᵢ = −m and Σ(u) > 0} ∪
{u : some uᵢ = +m and Σ(u) < 0}`"). -/
def InTri (u : CubeCell k) : Prop :=
  (∃ i, coord k u i = -(m k : ℤ) ∧ Sigma k u > 0) ∨
  (∃ i, coord k u i = (m k : ℤ) ∧ Sigma k u < 0)

/-- The in-plane triangle coordinates of a cell of `Tri`, one case per face, matching
`notes/log.md`'s "for the face `u₁ = −m`: `a = m−u₂, b = m−u₃`" (and, by the `u ↦ −u` symmetry
noted there for the `Σ < 0` faces, `a = u_j + m` off the pinned coordinate). Defined on all of
`CubeCell k` for convenience (junk value off `Tri`); only its values on `Tri` are ever used.

Branches first on `Σ`'s sign, *then* which axis is pinned - not the other way around. Two
coordinates can sit at opposite extremes simultaneously (e.g. `u₀ = -m`, `u₂ = +m`, an edge
where two corner faces of the cube meet), and `InTri`'s own two disjuncts are already keyed on
`Σ`'s sign; checking `-m` conditions before any `+m` condition regardless of sign picked the
wrong face on exactly such edges, producing an `(a, b)` whose sum isn't `< m` after all. -/
noncomputable def triCoord (u : CubeCell k) : ℕ × ℕ :=
  if Sigma k u > 0 then
    if coord k u 0 = -(m k : ℤ) then
      (((m k : ℤ) - coord k u 1).toNat, ((m k : ℤ) - coord k u 2).toNat)
    else if coord k u 1 = -(m k : ℤ) then
      (((m k : ℤ) - coord k u 0).toNat, ((m k : ℤ) - coord k u 2).toNat)
    else
      (((m k : ℤ) - coord k u 0).toNat, ((m k : ℤ) - coord k u 1).toNat)
  else
    if coord k u 0 = (m k : ℤ) then
      ((coord k u 1 + (m k : ℤ)).toNat, (coord k u 2 + (m k : ℤ)).toNat)
    else if coord k u 1 = (m k : ℤ) then
      ((coord k u 0 + (m k : ℤ)).toNat, (coord k u 2 + (m k : ℤ)).toNat)
    else
      ((coord k u 0 + (m k : ℤ)).toNat, (coord k u 1 + (m k : ℤ)).toNat)

/-- The single witness function for the whole cube (`notes/log.md`'s `L`): `ell m (triCoord u)`
on `Tri`, `|Σ(u)|` off it. -/
noncomputable def L (u : CubeCell k) : ℕ :=
  if InTri k u then ell (m k) (triCoord k u) else (Sigma k u).natAbs

/-- The claimed minimal percolating set `Aₙ`: the hexagon `H` together with, on each triangular
face, the zero-locus of `ell m` (i.e. `Pmem m`, via `triCoord`). -/
noncomputable def Aset : Finset (CubeCell k) :=
  Finset.univ.filter (fun u => InH k u ∨ (InTri k u ∧ Pmem (m k) (triCoord k u)))

/-- Centered coordinates are always in `[-m, m]`, since `u i : Fin (n k)` and
`n k = 2 * m k + 1`. -/
lemma coord_bounds (u : CubeCell k) (i : Fin 3) :
    -(m k : ℤ) ≤ coord k u i ∧ coord k u i ≤ (m k : ℤ) := by
  unfold coord
  have h : (u i : ℕ) < n k := (u i).isLt
  unfold n at h
  omega

/-- A cell of `Tri` always lands in `Δ_m`'s domain: its triangle coordinates sum to
strictly less than `m`. `triCoord`'s outer branch (on `Σ`'s sign) is resolved first, directly
from `hSig` - this is what rules out the problematic "two opposite extremes at once" edge case
(see `triCoord`'s doc comment). Within the matching sign, the inner 3-way split on which axis is
pinned is handled uniformly: either it contradicts the branch actually taken (`coord_bounds`
forcing the other two coordinates too far from the extreme for `Σ` to have the needed sign,
*now* always within a single, consistent sign), or it gives the bound directly. -/
lemma triCoord_sum_lt (u : CubeCell k) (hTri : InTri k u) :
    (triCoord k u).1 + (triCoord k u).2 < m k := by
  have hb0 := coord_bounds k u 0
  have hb1 := coord_bounds k u 1
  have hb2 := coord_bounds k u 2
  have hidx : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  unfold triCoord
  rcases hTri with ⟨i, hi, hSig⟩ | ⟨i, hi, hSig⟩
  · rw [if_pos hSig]
    unfold Sigma at hSig
    rcases hidx i with hi3 | hi3 | hi3 <;> subst hi3 <;> split_ifs <;> omega
  · rw [if_neg (by omega)]
    unfold Sigma at hSig
    rcases hidx i with hi3 | hi3 | hi3 <;> subst hi3 <;> split_ifs <;> omega

/-- **Lemma 2, part 1.** `L` vanishes exactly on `Aset`. -/
theorem L_eq_zero_iff (u : CubeCell k) : L k u = 0 ↔ u ∈ Aset k := by
  unfold Aset
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  unfold L
  by_cases hTri : InTri k u
  · rw [if_pos hTri]
    have hNotH : ¬ InH k u := by
      unfold InH
      rcases hTri with ⟨i, hi, hSig⟩ | ⟨i, hi, hSig⟩ <;> omega
    constructor
    · intro h0
      exact Or.inr ⟨hTri, (Lemma1Triangle.ell_eq_zero_iff k (triCoord k u).1 (triCoord k u).2
        (triCoord_sum_lt k u hTri)).mp h0⟩
    · intro h
      rcases h with hH | ⟨_, hP⟩
      · exact absurd hH hNotH
      · exact (Lemma1Triangle.ell_eq_zero_iff k (triCoord k u).1 (triCoord k u).2
          (triCoord_sum_lt k u hTri)).mpr hP
  · rw [if_neg hTri]
    constructor
    · intro h0
      exact Or.inl (Int.natAbs_eq_zero.mp h0)
    · intro h
      rcases h with hH | ⟨hT, _⟩
      · exact Int.natAbs_eq_zero.mpr hH
      · exact absurd hT hTri

/-- **Lemma 2, part 2.** `L ≤ 3m` everywhere (`notes/log.md`: "`L ≤ |Σ| ≤ 3m`, with equality at
the corners"). This is all the certificate corollary below needs; the matching equality case
(a corner cell with `L = 3m`) is not needed for the upper bound and is deferred. -/
theorem L_le_three_m (u : CubeCell k) : L k u ≤ 3 * m k := by
  unfold L
  by_cases hTri : InTri k u
  · rw [if_pos hTri]
    have hab := triCoord_sum_lt k u hTri
    have hle := Lemma1Triangle.ell_le_remaining k (triCoord k u).1 (triCoord k u).2 (by omega)
    -- `m k` is definitionally `mOf k`, and `triCoord k u` is definitionally the pair of its own
    -- components, but neither is *syntactically* so - omega treats `ell (m k) (triCoord k u)`
    -- and `ell (mOf k) ((triCoord k u).1, (triCoord k u).2)` (hle's LHS) as unrelated opaque
    -- atoms unless handed the bridging equations directly, as plain `rfl` facts.
    have heq : ell (m k) (triCoord k u) = ell (mOf k) ((triCoord k u).1, (triCoord k u).2) := rfl
    have hmeq : m k = mOf k := rfl
    omega
  · rw [if_neg hTri]
    unfold Sigma
    have hb0 := coord_bounds k u 0
    have hb1 := coord_bounds k u 1
    have hb2 := coord_bounds k u 2
    omega

/-- If `u` and `v` agree off a single index `j`, and differ there by exactly `1`, they are
grid-adjacent. The one genuinely case-heavy step (which of the three `Fin 3` indices `j` is)
is isolated here so `decAt`/`incAt` below can both reuse it directly. -/
lemma adjacent_of_eq_succ_at (u v : CubeCell k) (j : Fin 3)
    (hj : (u j : ℕ) = (v j : ℕ) + 1 ∨ (v j : ℕ) = (u j : ℕ) + 1)
    (hother : ∀ i, i ≠ j → (u i : ℕ) = (v i : ℕ)) : adjacent u v := by
  unfold adjacent mdist
  rw [Fin.sum_univ_three]
  have key : ∀ i, i ≠ j → (((u i : ℕ) : ℤ) - ((v i : ℕ) : ℤ)).natAbs = 0 := by
    intro i hi; have := hother i hi; omega
  have keyj : (((u j : ℕ) : ℤ) - ((v j : ℕ) : ℤ)).natAbs = 1 := by omega
  fin_cases j
  · have e1 := key 1 (by decide)
    have e2 := key 2 (by decide)
    omega
  · have e1 := key 0 (by decide)
    have e2 := key 2 (by decide)
    omega
  · have e1 := key 0 (by decide)
    have e2 := key 1 (by decide)
    omega

/-- `u` with its `j`-th grid coordinate decreased by `1`, when that stays `≥ 0`. -/
def decAt (u : CubeCell k) (j : Fin 3) (h : 1 ≤ (u j : ℕ)) : CubeCell k :=
  fun i => if i = j then (⟨(u j : ℕ) - 1, by have := (u j).isLt; omega⟩ : Fin (n k)) else u i

lemma decAt_self (u : CubeCell k) (j : Fin 3) (h : 1 ≤ (u j : ℕ)) :
    ((decAt k u j h) j : ℕ) = (u j : ℕ) - 1 := by
  unfold decAt; rw [if_pos rfl]

lemma decAt_other (u : CubeCell k) (j : Fin 3) (h : 1 ≤ (u j : ℕ)) (i : Fin 3) (hij : i ≠ j) :
    (decAt k u j h) i = u i := by
  unfold decAt; rw [if_neg hij]

lemma adjacent_decAt (u : CubeCell k) (j : Fin 3) (h : 1 ≤ (u j : ℕ)) :
    adjacent u (decAt k u j h) := by
  apply adjacent_of_eq_succ_at k u (decAt k u j h) j
  · left; rw [decAt_self k u j h]; omega
  · intro i hi; rw [decAt_other k u j h i hi]

lemma coord_decAt_self (u : CubeCell k) (j : Fin 3) (h : 1 ≤ (u j : ℕ)) :
    coord k (decAt k u j h) j = coord k u j - 1 := by
  unfold coord; have e := decAt_self k u j h; omega

lemma coord_decAt_other (u : CubeCell k) (j : Fin 3) (h : 1 ≤ (u j : ℕ)) (i : Fin 3)
    (hij : i ≠ j) : coord k (decAt k u j h) i = coord k u i := by
  unfold coord; rw [decAt_other k u j h i hij]

lemma Sigma_decAt (u : CubeCell k) (j : Fin 3) (h : 1 ≤ (u j : ℕ)) :
    Sigma k (decAt k u j h) = Sigma k u - 1 := by
  unfold Sigma
  fin_cases j
  · rw [coord_decAt_self k u 0 h, coord_decAt_other k u 0 h 1 (by decide),
      coord_decAt_other k u 0 h 2 (by decide)]; ring
  · rw [coord_decAt_other k u 1 h 0 (by decide), coord_decAt_self k u 1 h,
      coord_decAt_other k u 1 h 2 (by decide)]; ring
  · rw [coord_decAt_other k u 2 h 0 (by decide), coord_decAt_other k u 2 h 1 (by decide),
      coord_decAt_self k u 2 h]; ring

/-- `u` with its `j`-th grid coordinate increased by `1`, when that stays `< n`. -/
def incAt (u : CubeCell k) (j : Fin 3) (h : (u j : ℕ) + 1 < n k) : CubeCell k :=
  fun i => if i = j then (⟨(u j : ℕ) + 1, h⟩ : Fin (n k)) else u i

lemma incAt_self (u : CubeCell k) (j : Fin 3) (h : (u j : ℕ) + 1 < n k) :
    ((incAt k u j h) j : ℕ) = (u j : ℕ) + 1 := by
  unfold incAt; rw [if_pos rfl]

lemma incAt_other (u : CubeCell k) (j : Fin 3) (h : (u j : ℕ) + 1 < n k) (i : Fin 3)
    (hij : i ≠ j) : (incAt k u j h) i = u i := by
  unfold incAt; rw [if_neg hij]

lemma adjacent_incAt (u : CubeCell k) (j : Fin 3) (h : (u j : ℕ) + 1 < n k) :
    adjacent u (incAt k u j h) := by
  apply adjacent_of_eq_succ_at k u (incAt k u j h) j
  · right; rw [incAt_self k u j h]
  · intro i hi; rw [incAt_other k u j h i hi]

lemma coord_incAt_self (u : CubeCell k) (j : Fin 3) (h : (u j : ℕ) + 1 < n k) :
    coord k (incAt k u j h) j = coord k u j + 1 := by
  unfold coord; have e := incAt_self k u j h; omega

lemma coord_incAt_other (u : CubeCell k) (j : Fin 3) (h : (u j : ℕ) + 1 < n k) (i : Fin 3)
    (hij : i ≠ j) : coord k (incAt k u j h) i = coord k u i := by
  unfold coord; rw [incAt_other k u j h i hij]

lemma Sigma_incAt (u : CubeCell k) (j : Fin 3) (h : (u j : ℕ) + 1 < n k) :
    Sigma k (incAt k u j h) = Sigma k u + 1 := by
  unfold Sigma
  fin_cases j
  · rw [coord_incAt_self k u 0 h, coord_incAt_other k u 0 h 1 (by decide),
      coord_incAt_other k u 0 h 2 (by decide)]; ring
  · rw [coord_incAt_other k u 1 h 0 (by decide), coord_incAt_self k u 1 h,
      coord_incAt_other k u 1 h 2 (by decide)]; ring
  · rw [coord_incAt_other k u 2 h 0 (by decide), coord_incAt_other k u 2 h 1 (by decide),
      coord_incAt_self k u 2 h]; ring

/-! The off-`Tri` case of claim 3 (`notes/log.md`: "A cell `u ∉ Tri` with `s = Σ(u) > 0`: its
three neighbours `u − eᵢ` exist and have `Σ = s − 1`; each lies in `H` (`s = 1`), or outside
`Tri` with `L = s − 1`, or in `Tri` with `L = ℓ_m ≤ Σ = s − 1` by Lemma 1(i)") is not yet
written up in Lean - `decAt`/`incAt` and their `coord`/`Sigma` lemmas above are exactly the
grid mechanics it needs (`u - eᵢ` is `decAt k u i _`, `u + eᵢ` is `incAt k u i _`); what remains
is the case split above on whether each of the three shifted cells lands back in `Tri`, which
needs identifying *which* face of `Tri` it can possibly land on (at most the axis just shifted,
since `u ∉ Tri` already rules out every other coordinate being pinned) before `Lemma1ClaimI`'s
bound applies. The on-`Tri` case (`notes/log.md`'s Lemma 1(ii) via `triCoord`, plus the
hypotenuse-crosses-into-`H` sub-case) is the other, harder half. -/

/-- **Lemma 2, part 3.** Every cell with `L > 0` has at least 3 of its (cube-)neighbours with
strictly smaller `L` - the hypothesis `BootstrapPercolation.certificate` needs, specialised to
`d = 3`. -/
theorem three_smaller_neighbours (u : CubeCell k) (hu : L k u ≠ 0) :
    3 ≤ (Finset.univ.filter (fun v => adjacent u v ∧ L k v < L k u)).card := by
  sorry

/-- Corollary (`notes/log.md`'s certificate, applied to `Aset`/`L`): `Aset` percolates. -/
theorem Aset_percolates : Percolates (Aset k) :=
  percolates_of_certificate (Aset k) (L k) (fun u => (L_eq_zero_iff k u).symm)
    (three_smaller_neighbours k)

/-- Corollary: `Aset` percolates in at most `3m` rounds (the certificate's `T(A) ≤ max L`,
matching `notes/log.md`'s "`T ≤ max L = 3m`"). -/
theorem Aset_afterRounds_three_m : afterRounds (Aset k) (3 * m k) = Finset.univ :=
  Finset.eq_univ_of_forall fun u =>
    certificate (Aset k) (L k) (fun v => (L_eq_zero_iff k v).symm) (three_smaller_neighbours k)
      (3 * m k) u (L_le_three_m k u)

end BootstrapPercolation.Lemma2Cube
