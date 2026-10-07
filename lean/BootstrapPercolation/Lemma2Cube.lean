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
    -- `m k` is definitionally `mOf k` (needed *before* `ell_le_remaining`'s own hypothesis
    -- below, which is itself discharged by `omega` and needs this bridge too), and
    -- `triCoord k u` is definitionally the pair of its own components - neither is
    -- *syntactically* so, so omega treats `ell (m k) (triCoord k u)` and
    -- `ell (mOf k) ((triCoord k u).1, (triCoord k u).2)` (hle's LHS) as unrelated opaque atoms
    -- unless handed the bridging equations directly, as plain `rfl` facts.
    have hmeq : m k = mOf k := rfl
    have hle := Lemma1Triangle.ell_le_remaining k (triCoord k u).1 (triCoord k u).2 (by omega)
    have heq : ell (m k) (triCoord k u) = ell (mOf k) ((triCoord k u).1, (triCoord k u).2) := rfl
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
  have hidx : ∀ j' : Fin 3, j' = 0 ∨ j' = 1 ∨ j' = 2 := by decide
  rcases hidx j with hj3 | hj3 | hj3 <;> subst hj3
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
  have hidx : ∀ j' : Fin 3, j' = 0 ∨ j' = 1 ∨ j' = 2 := by decide
  unfold Sigma
  rcases hidx j with hj3 | hj3 | hj3 <;> subst hj3
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
  have hidx : ∀ j' : Fin 3, j' = 0 ∨ j' = 1 ∨ j' = 2 := by decide
  unfold Sigma
  rcases hidx j with hj3 | hj3 | hj3 <;> subst hj3
  · rw [coord_incAt_self k u 0 h, coord_incAt_other k u 0 h 1 (by decide),
      coord_incAt_other k u 0 h 2 (by decide)]; ring
  · rw [coord_incAt_other k u 1 h 0 (by decide), coord_incAt_self k u 1 h,
      coord_incAt_other k u 1 h 2 (by decide)]; ring
  · rw [coord_incAt_other k u 2 h 0 (by decide), coord_incAt_other k u 2 h 1 (by decide),
      coord_incAt_self k u 2 h]; ring

/-- When `w`'s pinned coordinate sits at `-m` (so, since `Σ(w) > 0`, `triCoord`'s outer
branch - see its doc comment - takes the `-m` side), the "remaining budget" `m - a - b` that
`Lemma1ClaimI.ell_le_remaining` bounds `ell` by works out to be exactly `Σ(w)`: whichever of
the three axes is actually pinned, the *other two* coordinates are what `a, b` are built from,
and their sum is `Σ(w) - (−m) - m = Σ(w)` once the pinned one (`= -m`) is subtracted out. -/
lemma triCoord_remaining_eq_sigma_pos (w : CubeCell k)
    (hw : ∃ i, coord k w i = -(m k : ℤ) ∧ Sigma k w > 0) :
    (m k : ℤ) - (triCoord k w).1 - (triCoord k w).2 = Sigma k w := by
  have hb0 := coord_bounds k w 0
  have hb1 := coord_bounds k w 1
  have hb2 := coord_bounds k w 2
  have hidx : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  unfold triCoord
  obtain ⟨i, hi, hSig⟩ := hw
  rw [if_pos hSig]
  unfold Sigma
  rcases hidx i with hi3 | hi3 | hi3 <;> subst hi3 <;> split_ifs <;> omega

/-- The `Σ(w) < 0` mirror of `triCoord_remaining_eq_sigma_pos` (`notes/log.md`'s `u ↦ -u`
symmetry for the `+m` faces): the remaining budget works out to `-Σ(w)` instead. -/
lemma triCoord_remaining_eq_sigma_neg (w : CubeCell k)
    (hw : ∃ i, coord k w i = (m k : ℤ) ∧ Sigma k w < 0) :
    (m k : ℤ) - (triCoord k w).1 - (triCoord k w).2 = -(Sigma k w) := by
  have hb0 := coord_bounds k w 0
  have hb1 := coord_bounds k w 1
  have hb2 := coord_bounds k w 2
  have hidx : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  unfold triCoord
  obtain ⟨i, hi, hSig⟩ := hw
  rw [if_neg (by omega)]
  unfold Sigma
  rcases hidx i with hi3 | hi3 | hi3 <;> subst hi3 <;> split_ifs <;> omega

/-- Combines `Lemma1ClaimI.ell_le_remaining` with the two lemmas above: on `Tri`, `ell`'s value
is bounded by `|Σ|`, matching one direction of `notes/log.md`'s "`L ≤ |Σ| ≤ 3m`" (the other
direction, `L = |Σ|` off `Tri`, is immediate from `L`'s own definition). -/
lemma ell_triCoord_le_sigma_natAbs (w : CubeCell k) (hTw : InTri k w) :
    ell (m k) (triCoord k w) ≤ (Sigma k w).natAbs := by
  have hsum := triCoord_sum_lt k w hTw
  have hmeq : m k = mOf k := rfl
  have hle := Lemma1Triangle.ell_le_remaining k (triCoord k w).1 (triCoord k w).2 (by omega)
  have heq : ell (m k) (triCoord k w) = ell (mOf k) ((triCoord k w).1, (triCoord k w).2) := rfl
  rcases hTw with hw | hw
  · obtain ⟨i, hi, hsign⟩ := hw
    have hrem := triCoord_remaining_eq_sigma_pos k w ⟨i, hi, hsign⟩
    omega
  · obtain ⟨i, hi, hsign⟩ := hw
    have hrem := triCoord_remaining_eq_sigma_neg k w ⟨i, hi, hsign⟩
    omega

/-- `L` is bounded by `|Σ|` *everywhere*, not just off `Tri` (where it's equal by definition) -
the uniform bound the off-`Tri` case of claim 3 needs below, since a shifted neighbour can land
on either side of `Tri`'s boundary and this covers both without a case split there. -/
lemma L_le_sigma_natAbs (w : CubeCell k) : L k w ≤ (Sigma k w).natAbs := by
  unfold L
  by_cases hTw : InTri k w
  · rw [if_pos hTw]; exact ell_triCoord_le_sigma_natAbs k w hTw
  · rw [if_neg hTw]

/-- The in-plane-neighbour image, for a cell `w` pinned at axis `i0`'s complement `j1, j2`
to `-m`: matches `notes/log.md`'s identification of `Δ_m`'s in-plane neighbours `(a±1,b)`,
`(a,b±1)` with the cube's actual grid neighbours obtained by shifting `j1`/`j2` (never `i0` -
"the cell above is simply not used"). Increasing a triangle coordinate *decreases* the
matching cube coordinate (since `a = m - coord j`), so `(a+1,b)`/`(a,b+1)` are `decAt`
and `(a-1,b)`/`(a,b-1)` are `incAt`. Total (defaults to `w` off these four exact points,
which the proof below shows is never actually reached for a genuine neighbour of a cell
satisfying `triCoord_sum_lt`). -/
noncomputable def faceNegImage (w : CubeCell k) (j1 j2 : Fin 3) (a b : ℕ) (p : ℕ × ℕ) :
    CubeCell k :=
  if p.1 = a + 1 then
    (if h : 1 ≤ (w j1 : ℕ) then decAt k w j1 h else w)
  else if p.2 = b + 1 then
    (if h : 1 ≤ (w j2 : ℕ) then decAt k w j2 h else w)
  else if p.1 + 1 = a then
    (if h : (w j1 : ℕ) + 1 < n k then incAt k w j1 h else w)
  else
    (if h : (w j2 : ℕ) + 1 < n k then incAt k w j2 h else w)

/-- **One face of the on-`Tri` case of claim 3**, for whichever axis `i0` is pinned to `-m`
(`j1, j2` the other two). `hsigeq` records `Σ = coord i0 + coord j1 + coord j2` and `htriv`
records which branch of `triCoord` fires for any cell pinned the same way at `i0` - both
trivial (`ring`-level) facts about the *concrete* `i0, j1, j2` at each of the three call
sites, which is why they are left as hypotheses here rather than re-derived generically
(`triCoord`'s own definition checks axis `0`, then `1`, then `2`, so "which branch fires"
is not expressible for an abstract `i0`). Combines `Lemma1Triangle.three_smaller_neighbours`
(claim (ii): ≥3 in-plane neighbours of smaller `ell` in `Δ_m`) with `faceNegImage`'s key
property - proved by the `mem_neighbors` case split below - that it always lands on the cell
whose `j1`/`j2` coordinates are exactly `m - p.1`/`m - p.2`: this lets a shifted cell's own
label be read off directly, whether it stays on the same face (`p.1 + p.2 < m`, giving
`ell (p.1, p.2)` again) or crosses the hypotenuse into `H` (`p.1 + p.2 = m`, giving `L = 0`,
trivially smaller). -/
lemma three_smaller_neighbours_face_neg (w : CubeCell k) (i0 j1 j2 : Fin 3)
    (h01 : i0 ≠ j1) (h02 : i0 ≠ j2) (h12 : j1 ≠ j2)
    (hsigeq : ∀ v : CubeCell k, Sigma k v = coord k v i0 + coord k v j1 + coord k v j2)
    (htriv : ∀ v : CubeCell k, coord k v i0 = -(m k : ℤ) → Sigma k v > 0 →
      triCoord k v = (((m k : ℤ) - coord k v j1).toNat, ((m k : ℤ) - coord k v j2).toNat))
    (hpin : coord k w i0 = -(m k : ℤ)) (hsig : Sigma k w > 0) (hu : L k w ≠ 0) :
    3 ≤ (Finset.univ.filter (fun v => adjacent w v ∧ L k v < L k w)).card := by
  have hTw : InTri k w := Or.inl ⟨i0, hpin, hsig⟩
  have hb1 := coord_bounds k w j1
  have hb2 := coord_bounds k w j2
  have htc := htriv w hpin hsig
  have hLw : L k w = ell (m k) (triCoord k w) := by unfold L; rw [if_pos hTw]
  have hab_lt := triCoord_sum_lt k w hTw
  rw [htc] at hab_lt hLw
  have hmeq : m k = mOf k := rfl
  have heqw : ell (m k) (((m k : ℤ) - coord k w j1).toNat, ((m k : ℤ) - coord k w j2).toNat) =
      ell (mOf k) (((m k : ℤ) - coord k w j1).toNat, ((m k : ℤ) - coord k w j2).toNat) := by
    rw [hmeq]
  have hpos : 0 < ell (mOf k) (((m k : ℤ) - coord k w j1).toNat, ((m k : ℤ) - coord k w j2).toNat) := by
    rw [hLw, heqw] at hu; omega
  have hLwpos : 0 < L k w := by rw [hLw, heqw]; omega
  set a := ((m k : ℤ) - coord k w j1).toNat with ha_def
  set b := ((m k : ℤ) - coord k w j2).toNat with hb_def
  have hS := Lemma1Triangle.three_smaller_neighbours k a b (by omega) hpos
  have hj1dec : 1 ≤ (w j1 : ℕ) := by
    by_contra hcon; push_neg at hcon
    have hv0 : (w j1 : ℕ) = 0 := by omega
    have hz : coord k w j1 = -(m k : ℤ) := by unfold coord; omega
    rw [hz] at ha_def; omega
  have hj2dec : 1 ≤ (w j2 : ℕ) := by
    by_contra hcon; push_neg at hcon
    have hv0 : (w j2 : ℕ) = 0 := by omega
    have hz : coord k w j2 = -(m k : ℤ) := by unfold coord; omega
    rw [hz] at hb_def; omega
  have hkey : ∀ p ∈ neighbors a b,
      coord k (faceNegImage k w j1 j2 a b p) j1 = (m k : ℤ) - (p.1 : ℤ) ∧
      coord k (faceNegImage k w j1 j2 a b p) j2 = (m k : ℤ) - (p.2 : ℤ) ∧
      coord k (faceNegImage k w j1 j2 a b p) i0 = -(m k : ℤ) ∧
      adjacent w (faceNegImage k w j1 j2 a b p) ∧
      p.1 + p.2 ≤ m k := by
    intro p hp
    rw [mem_neighbors] at hp
    unfold faceNegImage
    rcases hp with rfl | rfl | ⟨ha, rfl⟩ | ⟨hb, rfl⟩
    · rw [if_pos rfl, dif_pos hj1dec]
      refine ⟨?_, ?_, ?_, adjacent_decAt k w j1 hj1dec, by omega⟩
      · have e := coord_decAt_self k w j1 hj1dec; push_cast; omega
      · rw [coord_decAt_other k w j1 hj1dec j2 h12.symm]; push_cast; omega
      · rw [coord_decAt_other k w j1 hj1dec i0 (h01)]; exact hpin
    · rw [if_neg (by omega), if_pos rfl, dif_pos hj2dec]
      refine ⟨?_, ?_, ?_, adjacent_decAt k w j2 hj2dec, by omega⟩
      · rw [coord_decAt_other k w j2 hj2dec j1 h12]; push_cast; omega
      · have e := coord_decAt_self k w j2 hj2dec; push_cast; omega
      · rw [coord_decAt_other k w j2 hj2dec i0 (h02)]; exact hpin
    · have hj1inc : (w j1 : ℕ) + 1 < n k := by
        have hcj1 : coord k w j1 = ((w j1 : ℕ) : ℤ) - (m k : ℤ) := rfl
        unfold n; omega
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), dif_pos hj1inc]
      refine ⟨?_, ?_, ?_, adjacent_incAt k w j1 hj1inc, by omega⟩
      · have e := coord_incAt_self k w j1 hj1inc; push_cast; omega
      · rw [coord_incAt_other k w j1 hj1inc j2 h12.symm]; push_cast; omega
      · rw [coord_incAt_other k w j1 hj1inc i0 (h01)]; exact hpin
    · have hj2inc : (w j2 : ℕ) + 1 < n k := by
        have hcj2 : coord k w j2 = ((w j2 : ℕ) : ℤ) - (m k : ℤ) := rfl
        unfold n; omega
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_pos hj2inc]
      refine ⟨?_, ?_, ?_, adjacent_incAt k w j2 hj2inc, by omega⟩
      · rw [coord_incAt_other k w j2 hj2inc j1 h12]; push_cast; omega
      · have e := coord_incAt_self k w j2 hj2inc; push_cast; omega
      · rw [coord_incAt_other k w j2 hj2inc i0 (h02)]; exact hpin
  have hinj : Set.InjOn (faceNegImage k w j1 j2 a b) (neighbors a b) := by
    intro p hp q hq heq
    obtain ⟨hp1, hp2, _, _, _⟩ := hkey p hp
    obtain ⟨hq1, hq2, _, _, _⟩ := hkey q hq
    rw [heq] at hp1 hp2
    have e1 : p.1 = q.1 := by omega
    have e2 : p.2 = q.2 := by omega
    exact Prod.ext e1 e2
  have hmapsto : ∀ p ∈ (neighbors a b).filter (fun v => ell (mOf k) v < ell (mOf k) (a, b)),
      faceNegImage k w j1 j2 a b p ∈ Finset.univ.filter (fun v => adjacent w v ∧ L k v < L k w) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpmem, hplt⟩ := hp
    obtain ⟨hcj1, hcj2, hci0, hadj, hpsum⟩ := hkey p hpmem
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hadj, ?_⟩
    rcases lt_or_eq_of_le hpsum with hlt | heqm
    · have hSigpos : Sigma k (faceNegImage k w j1 j2 a b p) > 0 := by
        rw [hsigeq]; omega
      have htcv : triCoord k (faceNegImage k w j1 j2 a b p) = (p.1, p.2) := by
        have hbase := htriv _ hci0 hSigpos
        rw [hbase]
        have e1 : ((m k : ℤ) - coord k (faceNegImage k w j1 j2 a b p) j1).toNat = p.1 := by omega
        have e2 : ((m k : ℤ) - coord k (faceNegImage k w j1 j2 a b p) j2).toNat = p.2 := by omega
        rw [e1, e2]
      have hivT : InTri k (faceNegImage k w j1 j2 a b p) := Or.inl ⟨i0, hci0, hSigpos⟩
      have hLv : L k (faceNegImage k w j1 j2 a b p) = ell (mOf k) p := by
        unfold L
        rw [if_pos hivT, htcv, hmeq]
      rw [hLv]
      omega
    · have hSigeq0 : Sigma k (faceNegImage k w j1 j2 a b p) = 0 := by
        rw [hsigeq]; omega
      have hnTv : ¬ InTri k (faceNegImage k w j1 j2 a b p) := by
        rintro (⟨i, _, hs⟩ | ⟨i, _, hs⟩) <;> omega
      have hLv0 : L k (faceNegImage k w j1 j2 a b p) = 0 := by
        unfold L; rw [if_neg hnTv, hSigeq0]; decide
      rw [hLv0]
      omega
  have hcard := Finset.card_le_card_of_injOn (faceNegImage k w j1 j2 a b) hmapsto
    (hinj.mono (Finset.filter_subset _ _))
  omega

/-- **Lemma 2, part 3.** Every cell with `L > 0` has at least 3 of its (cube-)neighbours with
strictly smaller `L` - the hypothesis `BootstrapPercolation.certificate` needs, specialised to
`d = 3`.

The off-`Tri` case (`notes/log.md`: "its three neighbours `u − eᵢ` exist and have
`Σ = s − 1`... `L ≤ |Σ|`... so each is `< L(u)`") is proved directly below via `decAt`/`incAt`
and `L_le_sigma_natAbs` - no need to track which face a shifted neighbour lands on, since that
lemma bounds `L` by `|Σ|` uniformly on both sides of `Tri`'s boundary. The on-`Tri` case
(`notes/log.md`'s Lemma 1(ii) via `triCoord`, plus the hypotenuse-crosses-into-`H` sub-case) is
the other, harder half, still `sorry`. -/
theorem three_smaller_neighbours (u : CubeCell k) (hu : L k u ≠ 0) :
    3 ≤ (Finset.univ.filter (fun v => adjacent u v ∧ L k v < L k u)).card := by
  by_cases hTri : InTri k u
  · sorry
  · have hLu : L k u = (Sigma k u).natAbs := by unfold L; rw [if_neg hTri]
    have hsne : Sigma k u ≠ 0 := by intro h; apply hu; rw [hLu, h]; decide
    rcases lt_or_gt_of_ne hsne with hneg | hpos
    · have h0 : (u 0 : ℕ) + 1 < n k := by
        by_contra hc; push_neg at hc
        have hlt := (u 0).isLt
        apply hTri; right; refine ⟨0, ?_, hneg⟩
        unfold coord; unfold n at hlt hc; omega
      have h1 : (u 1 : ℕ) + 1 < n k := by
        by_contra hc; push_neg at hc
        have hlt := (u 1).isLt
        apply hTri; right; refine ⟨1, ?_, hneg⟩
        unfold coord; unfold n at hlt hc; omega
      have h2 : (u 2 : ℕ) + 1 < n k := by
        by_contra hc; push_neg at hc
        have hlt := (u 2).isLt
        apply hTri; right; refine ⟨2, ?_, hneg⟩
        unfold coord; unfold n at hlt hc; omega
      have hadj0 := adjacent_incAt k u 0 h0
      have hadj1 := adjacent_incAt k u 1 h1
      have hadj2 := adjacent_incAt k u 2 h2
      have hS0 := Sigma_incAt k u 0 h0
      have hS1 := Sigma_incAt k u 1 h1
      have hS2 := Sigma_incAt k u 2 h2
      have hB0 := L_le_sigma_natAbs k (incAt k u 0 h0)
      have hB1 := L_le_sigma_natAbs k (incAt k u 1 h1)
      have hB2 := L_le_sigma_natAbs k (incAt k u 2 h2)
      have hL0 : L k (incAt k u 0 h0) < L k u := by rw [hLu]; omega
      have hL1 : L k (incAt k u 1 h1) < L k u := by rw [hLu]; omega
      have hL2 : L k (incAt k u 2 h2) < L k u := by rw [hLu]; omega
      have hv01 : incAt k u 0 h0 ≠ incAt k u 1 h1 := by
        intro heq
        have e0 : (incAt k u 0 h0 0 : ℕ) = (incAt k u 1 h1 0 : ℕ) := by rw [heq]
        rw [incAt_self k u 0 h0, incAt_other k u 1 h1 0 (by decide)] at e0
        omega
      have hv02 : incAt k u 0 h0 ≠ incAt k u 2 h2 := by
        intro heq
        have e0 : (incAt k u 0 h0 0 : ℕ) = (incAt k u 2 h2 0 : ℕ) := by rw [heq]
        rw [incAt_self k u 0 h0, incAt_other k u 2 h2 0 (by decide)] at e0
        omega
      have hv12 : incAt k u 1 h1 ≠ incAt k u 2 h2 := by
        intro heq
        have e0 : (incAt k u 1 h1 1 : ℕ) = (incAt k u 2 h2 1 : ℕ) := by rw [heq]
        rw [incAt_self k u 1 h1, incAt_other k u 2 h2 1 (by decide)] at e0
        omega
      have hsub : ({incAt k u 0 h0, incAt k u 1 h1, incAt k u 2 h2} : Finset (CubeCell k)) ⊆
          Finset.univ.filter (fun v => adjacent u v ∧ L k v < L k u) := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ v, ?_⟩
        rcases hv with h | h | h <;> subst h
        · exact ⟨hadj0, hL0⟩
        · exact ⟨hadj1, hL1⟩
        · exact ⟨hadj2, hL2⟩
      have hcard : ({incAt k u 0 h0, incAt k u 1 h1, incAt k u 2 h2} : Finset (CubeCell k)).card = 3 := by
        rw [Finset.card_eq_three]
        exact ⟨_, _, _, hv01, hv02, hv12, rfl⟩
      exact hcard.symm.le.trans (Finset.card_le_card hsub)
    · have h0 : 1 ≤ (u 0 : ℕ) := by
        rcases Nat.eq_zero_or_pos (u 0 : ℕ) with hz | hp
        · exact absurd (Or.inl ⟨0, by unfold coord; omega, hpos⟩ : InTri k u) hTri
        · exact hp
      have h1 : 1 ≤ (u 1 : ℕ) := by
        rcases Nat.eq_zero_or_pos (u 1 : ℕ) with hz | hp
        · exact absurd (Or.inl ⟨1, by unfold coord; omega, hpos⟩ : InTri k u) hTri
        · exact hp
      have h2 : 1 ≤ (u 2 : ℕ) := by
        rcases Nat.eq_zero_or_pos (u 2 : ℕ) with hz | hp
        · exact absurd (Or.inl ⟨2, by unfold coord; omega, hpos⟩ : InTri k u) hTri
        · exact hp
      have hadj0 := adjacent_decAt k u 0 h0
      have hadj1 := adjacent_decAt k u 1 h1
      have hadj2 := adjacent_decAt k u 2 h2
      have hS0 := Sigma_decAt k u 0 h0
      have hS1 := Sigma_decAt k u 1 h1
      have hS2 := Sigma_decAt k u 2 h2
      have hB0 := L_le_sigma_natAbs k (decAt k u 0 h0)
      have hB1 := L_le_sigma_natAbs k (decAt k u 1 h1)
      have hB2 := L_le_sigma_natAbs k (decAt k u 2 h2)
      have hL0 : L k (decAt k u 0 h0) < L k u := by rw [hLu]; omega
      have hL1 : L k (decAt k u 1 h1) < L k u := by rw [hLu]; omega
      have hL2 : L k (decAt k u 2 h2) < L k u := by rw [hLu]; omega
      have hv01 : decAt k u 0 h0 ≠ decAt k u 1 h1 := by
        intro heq
        have e0 : (decAt k u 0 h0 0 : ℕ) = (decAt k u 1 h1 0 : ℕ) := by rw [heq]
        rw [decAt_self k u 0 h0, decAt_other k u 1 h1 0 (by decide)] at e0
        omega
      have hv02 : decAt k u 0 h0 ≠ decAt k u 2 h2 := by
        intro heq
        have e0 : (decAt k u 0 h0 0 : ℕ) = (decAt k u 2 h2 0 : ℕ) := by rw [heq]
        rw [decAt_self k u 0 h0, decAt_other k u 2 h2 0 (by decide)] at e0
        omega
      have hv12 : decAt k u 1 h1 ≠ decAt k u 2 h2 := by
        intro heq
        have e0 : (decAt k u 1 h1 1 : ℕ) = (decAt k u 2 h2 1 : ℕ) := by rw [heq]
        rw [decAt_self k u 1 h1, decAt_other k u 2 h2 1 (by decide)] at e0
        omega
      have hsub : ({decAt k u 0 h0, decAt k u 1 h1, decAt k u 2 h2} : Finset (CubeCell k)) ⊆
          Finset.univ.filter (fun v => adjacent u v ∧ L k v < L k u) := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ v, ?_⟩
        rcases hv with h | h | h <;> subst h
        · exact ⟨hadj0, hL0⟩
        · exact ⟨hadj1, hL1⟩
        · exact ⟨hadj2, hL2⟩
      have hcard : ({decAt k u 0 h0, decAt k u 1 h1, decAt k u 2 h2} : Finset (CubeCell k)).card = 3 := by
        rw [Finset.card_eq_three]
        exact ⟨_, _, _, hv01, hv02, hv12, rfl⟩
      exact hcard.symm.le.trans (Finset.card_le_card hsub)

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
