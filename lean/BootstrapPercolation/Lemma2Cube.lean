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
`CubeCell k` for convenience (junk value off `Tri`); only its values on `Tri` are ever used. -/
noncomputable def triCoord (u : CubeCell k) : ℕ × ℕ :=
  if coord k u 0 = -(m k : ℤ) then
    (((m k : ℤ) - coord k u 1).toNat, ((m k : ℤ) - coord k u 2).toNat)
  else if coord k u 1 = -(m k : ℤ) then
    (((m k : ℤ) - coord k u 0).toNat, ((m k : ℤ) - coord k u 2).toNat)
  else if coord k u 2 = -(m k : ℤ) then
    (((m k : ℤ) - coord k u 0).toNat, ((m k : ℤ) - coord k u 1).toNat)
  else if coord k u 0 = (m k : ℤ) then
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

/-- **Lemma 2, part 1.** `L` vanishes exactly on `Aset`. -/
theorem L_eq_zero_iff (u : CubeCell k) : L k u = 0 ↔ u ∈ Aset k := by
  sorry

/-- **Lemma 2, part 2.** `L ≤ 3m` everywhere (`notes/log.md`: "`L ≤ |Σ| ≤ 3m`, with equality at
the corners"). This is all the certificate corollary below needs; the matching equality case
(a corner cell with `L = 3m`) is not needed for the upper bound and is deferred. -/
theorem L_le_three_m (u : CubeCell k) : L k u ≤ 3 * m k := by
  sorry

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
