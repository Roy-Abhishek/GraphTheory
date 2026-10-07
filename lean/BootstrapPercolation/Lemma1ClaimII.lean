import Mathlib
import BootstrapPercolation.Lemma1Triangle

/-! # Lemma 1, claim (ii)

From `notes/log.md`: on `Δ_m`, every cell with `ell m (a, b) > 0` has at least 3 of its
(existing, i.e. nonnegative-coordinate) in-plane neighbours `(a±1,b)`, `(a,b±1)` with
strictly smaller `ell m` value. Stated for `a + b ≤ mOf k`, `m = mOf k`, matching claim
(i) - see `Lemma1Triangle.lean`'s family restriction.

Two cases, as in the notes: a *mixed-parity* cell, where the two even-even neighbours are
always `0` and the third comes from whichever side attains the `min` in rule (x); and an
*odd-odd* cell `w = (2i+1,2j+1)`, which needs the harder correspondence: at least 3 of
`(i,j)`'s neighbours `w'` at level `mOf k` have `ell (mOf k) w' < ell (mOf k) (i,j)`
(by `ih`), and each such `w'` - in the SAME direction - gives a neighbour of `w` at level
`mOf (k+1)` with smaller `ell`, because unfolding rule (x) at that neighbour always
reduces to `1 + min (2 * ell (mOf k) (i,j)) (2 * ell (mOf k) w')`. This "same direction"
map is injective (the 4 possible images are pairwise distinct), so the ≥3 count transfers
via `Finset.card_image_of_injOn` + `Finset.card_le_card`. -/

namespace BootstrapPercolation.Lemma1Triangle

/-- The (up to 4) candidate in-plane neighbours of `(a, b)` with nonnegative coordinates.
`ell` itself relies on Nat truncated subtraction silently duplicating `(a,b)`'s own
row/column when `a = 0` or `b = 0` (harmless there, since it's folded into a `min`);
`neighbors` instead filters those degenerate duplicates out explicitly, since here we need
the actual count of *distinct* existing neighbours. -/
def neighbors (a b : ℕ) : Finset (ℕ × ℕ) :=
  (if a ≥ 1 then {((a - 1, b) : ℕ × ℕ)} else ∅) ∪ {(a + 1, b)} ∪
  (if b ≥ 1 then {((a, b - 1) : ℕ × ℕ)} else ∅) ∪ {(a, b + 1)}

lemma mem_neighbors (a b : ℕ) (v : ℕ × ℕ) :
    v ∈ neighbors a b ↔
      v = (a + 1, b) ∨ v = (a, b + 1) ∨ (a ≥ 1 ∧ v = (a - 1, b)) ∨ (b ≥ 1 ∧ v = (a, b - 1)) := by
  unfold neighbors
  by_cases ha : a ≥ 1 <;> by_cases hb : b ≥ 1 <;> simp [ha, hb] <;> tauto

/-- Claim (ii). -/
theorem three_smaller_neighbours :
    ∀ k a b : ℕ, a + b ≤ mOf k → 0 < ell (mOf k) (a, b) →
      3 ≤ (neighbors a b |>.filter (fun v => ell (mOf k) v < ell (mOf k) (a, b))).card := by
  intro k
  induction k with
  | zero =>
      intro a b hab hpos
      exfalso
      have hm0 : mOf 0 = 0 := by norm_num [mOf]
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha; subst hb
      rw [hm0] at hpos
      simp [ell] at hpos
  | succ k ih =>
      intro a b hab hpos
      have hsucc : mOf (k + 1) = 2 * mOf k + 2 := mOf_succ k
      have hm0eq : mOf (k + 1) / 2 - 1 = mOf k := by omega
      have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
      have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases ha2 with ha2 | ha2 <;> rcases hb2 with hb2 | hb2
      · -- a, b both even: contradiction
        exfalso
        have hval : ell (mOf (k + 1)) (a, b) = 0 := by
          rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
        rw [hval] at hpos; omega
      · -- a even, b odd: mixed
        have hval : ell (mOf (k + 1)) (a, b) =
            1 + min (2 * ell (mOf k) (a / 2 - 1, b / 2)) (2 * ell (mOf k) (a / 2, b / 2)) := by
          rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
        rw [hval] at hpos ⊢
        set X := 2 * ell (mOf k) (a / 2 - 1, b / 2) with hXdef
        set Y := 2 * ell (mOf k) (a / 2, b / 2) with hYdef
        have e1 : ell (mOf (k + 1)) (a, b - 1) = 0 := by
          rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
        have e2 : ell (mOf (k + 1)) (a, b + 1) = 0 := by
          rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
        have hb1 : b ≥ 1 := by omega
        have hmemD : (a, b - 1) ∈ neighbors a b :=
          (mem_neighbors a b _).mpr (Or.inr (Or.inr (Or.inr ⟨hb1, rfl⟩)))
        have hmemU : (a, b + 1) ∈ neighbors a b := (mem_neighbors a b _).mpr (Or.inr (Or.inl rfl))
        have hmemR : (a + 1, b) ∈ neighbors a b := (mem_neighbors a b _).mpr (Or.inl rfl)
        rcases lt_or_ge X Y with hlt | hge
        · have ha1 : a ≥ 1 := by
            by_contra ha0
            have ha0' : a = 0 := by omega
            rw [hXdef, hYdef, ha0'] at hlt
            simp at hlt
          have e3 : ell (mOf (k + 1)) (a - 1, b) = X := by
            have step : ell (mOf (k + 1)) (a - 1, b) = 2 * ell (mOf k) ((a - 1) / 2, b / 2) := by
              rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
            rw [step, show (((a - 1) / 2, b / 2) : ℕ × ℕ) = (a / 2 - 1, b / 2) from
              Prod.ext (by omega) (by omega)]
          have hmemL : (a - 1, b) ∈ neighbors a b :=
            (mem_neighbors a b _).mpr (Or.inr (Or.inr (Or.inl ⟨ha1, rfl⟩)))
          have hcard : {((a, b - 1) : ℕ × ℕ), (a, b + 1), (a - 1, b)} ⊆
              (neighbors a b).filter (fun v => ell (mOf (k + 1)) v < 1 + min X Y) := by
            intro v hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl | rfl
            · exact Finset.mem_filter.mpr ⟨hmemD, by rw [e1]; omega⟩
            · exact Finset.mem_filter.mpr ⟨hmemU, by rw [e2]; omega⟩
            · exact Finset.mem_filter.mpr ⟨hmemL, by rw [e3]; omega⟩
          have hd1 : ((a, b - 1) : ℕ × ℕ) ≠ (a, b + 1) := by
            intro h; simp only [Prod.mk.injEq] at h; omega
          have hd2 : ((a, b - 1) : ℕ × ℕ) ≠ (a - 1, b) := by
            intro h; simp only [Prod.mk.injEq] at h; omega
          have hd3 : ((a, b + 1) : ℕ × ℕ) ≠ (a - 1, b) := by
            intro h; simp only [Prod.mk.injEq] at h; omega
          have hcard3 : ({((a, b - 1) : ℕ × ℕ), (a, b + 1), (a - 1, b)} :
              Finset (ℕ × ℕ)).card = 3 := by
            first
            | rw [Finset.card_insert_of_notMem (by simp [hd1, hd2]),
                Finset.card_insert_of_notMem (by simp [hd3]), Finset.card_singleton]
            | rw [Finset.card_insert_of_not_mem (by simp [hd1, hd2]),
                Finset.card_insert_of_not_mem (by simp [hd3]), Finset.card_singleton]
          calc (3 : ℕ) = ({((a, b - 1) : ℕ × ℕ), (a, b + 1), (a - 1, b)} :
                Finset (ℕ × ℕ)).card := hcard3.symm
            _ ≤ _ := Finset.card_le_card hcard
        · have e4 : ell (mOf (k + 1)) (a + 1, b) = Y := by
            have step : ell (mOf (k + 1)) (a + 1, b) = 2 * ell (mOf k) ((a + 1) / 2, b / 2) := by
              rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
            rw [step, show (((a + 1) / 2, b / 2) : ℕ × ℕ) = (a / 2, b / 2) from
              Prod.ext (by omega) (by omega)]
          have hd1 : ((a, b - 1) : ℕ × ℕ) ≠ (a, b + 1) := by
            intro h; simp only [Prod.mk.injEq] at h; omega
          have hd2 : ((a, b - 1) : ℕ × ℕ) ≠ (a + 1, b) := by
            intro h; simp only [Prod.mk.injEq] at h; omega
          have hd3 : ((a, b + 1) : ℕ × ℕ) ≠ (a + 1, b) := by
            intro h; simp only [Prod.mk.injEq] at h; omega
          have hcard : {((a, b - 1) : ℕ × ℕ), (a, b + 1), (a + 1, b)} ⊆
              (neighbors a b).filter (fun v => ell (mOf (k + 1)) v < 1 + min X Y) := by
            intro v hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl | rfl
            · exact Finset.mem_filter.mpr ⟨hmemD, by rw [e1]; omega⟩
            · exact Finset.mem_filter.mpr ⟨hmemU, by rw [e2]; omega⟩
            · exact Finset.mem_filter.mpr ⟨hmemR, by rw [e4]; omega⟩
          have hcard3 : ({((a, b - 1) : ℕ × ℕ), (a, b + 1), (a + 1, b)} :
              Finset (ℕ × ℕ)).card = 3 := by
            first
            | rw [Finset.card_insert_of_notMem (by simp [hd1, hd2]),
                Finset.card_insert_of_notMem (by simp [hd3]), Finset.card_singleton]
            | rw [Finset.card_insert_of_not_mem (by simp [hd1, hd2]),
                Finset.card_insert_of_not_mem (by simp [hd3]), Finset.card_singleton]
          calc (3 : ℕ) = ({((a, b - 1) : ℕ × ℕ), (a, b + 1), (a + 1, b)} :
                Finset (ℕ × ℕ)).card := hcard3.symm
            _ ≤ _ := Finset.card_le_card hcard
      · -- a odd, b even: mixed
        have hval : ell (mOf (k + 1)) (a, b) =
            1 + min (2 * ell (mOf k) (a / 2, b / 2 - 1)) (2 * ell (mOf k) (a / 2, b / 2)) := by
          rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
        rw [hval] at hpos ⊢
        set X := 2 * ell (mOf k) (a / 2, b / 2 - 1) with hXdef
        set Y := 2 * ell (mOf k) (a / 2, b / 2) with hYdef
        have e1 : ell (mOf (k + 1)) (a - 1, b) = 0 := by
          rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
        have e2 : ell (mOf (k + 1)) (a + 1, b) = 0 := by
          rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
        have ha1 : a ≥ 1 := by omega
        have hmemL : (a - 1, b) ∈ neighbors a b :=
          (mem_neighbors a b _).mpr (Or.inr (Or.inr (Or.inl ⟨ha1, rfl⟩)))
        have hmemR : (a + 1, b) ∈ neighbors a b := (mem_neighbors a b _).mpr (Or.inl rfl)
        have hmemU : (a, b + 1) ∈ neighbors a b := (mem_neighbors a b _).mpr (Or.inr (Or.inl rfl))
        rcases lt_or_ge X Y with hlt | hge
        · have hb1 : b ≥ 1 := by
            by_contra hb0
            have hb0' : b = 0 := by omega
            rw [hXdef, hYdef, hb0'] at hlt
            simp at hlt
          have e3 : ell (mOf (k + 1)) (a, b - 1) = X := by
            have step : ell (mOf (k + 1)) (a, b - 1) = 2 * ell (mOf k) (a / 2, (b - 1) / 2) := by
              rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
            rw [step, show ((a / 2, (b - 1) / 2) : ℕ × ℕ) = (a / 2, b / 2 - 1) from
              Prod.ext (by omega) (by omega)]
          have hmemD : (a, b - 1) ∈ neighbors a b :=
            (mem_neighbors a b _).mpr (Or.inr (Or.inr (Or.inr ⟨hb1, rfl⟩)))
          have hd1 : ((a - 1, b) : ℕ × ℕ) ≠ (a + 1, b) := by
            intro h; simp only [Prod.mk.injEq] at h; omega
          have hd2 : ((a - 1, b) : ℕ × ℕ) ≠ (a, b - 1) := by
            intro h; simp only [Prod.mk.injEq] at h; omega
          have hd3 : ((a + 1, b) : ℕ × ℕ) ≠ (a, b - 1) := by
            intro h; simp only [Prod.mk.injEq] at h; omega
          have hcard : {((a - 1, b) : ℕ × ℕ), (a + 1, b), (a, b - 1)} ⊆
              (neighbors a b).filter (fun v => ell (mOf (k + 1)) v < 1 + min X Y) := by
            intro v hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl | rfl
            · exact Finset.mem_filter.mpr ⟨hmemL, by rw [e1]; omega⟩
            · exact Finset.mem_filter.mpr ⟨hmemR, by rw [e2]; omega⟩
            · exact Finset.mem_filter.mpr ⟨hmemD, by rw [e3]; omega⟩
          have hcard3 : ({((a - 1, b) : ℕ × ℕ), (a + 1, b), (a, b - 1)} :
              Finset (ℕ × ℕ)).card = 3 := by
            first
            | rw [Finset.card_insert_of_notMem (by simp [hd1, hd2]),
                Finset.card_insert_of_notMem (by simp [hd3]), Finset.card_singleton]
            | rw [Finset.card_insert_of_not_mem (by simp [hd1, hd2]),
                Finset.card_insert_of_not_mem (by simp [hd3]), Finset.card_singleton]
          calc (3 : ℕ) = ({((a - 1, b) : ℕ × ℕ), (a + 1, b), (a, b - 1)} :
                Finset (ℕ × ℕ)).card := hcard3.symm
            _ ≤ _ := Finset.card_le_card hcard
        · have e4 : ell (mOf (k + 1)) (a, b + 1) = Y := by
            have step : ell (mOf (k + 1)) (a, b + 1) = 2 * ell (mOf k) (a / 2, (b + 1) / 2) := by
              rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
            rw [step, show ((a / 2, (b + 1) / 2) : ℕ × ℕ) = (a / 2, b / 2) from
              Prod.ext (by omega) (by omega)]
          have hd1 : ((a - 1, b) : ℕ × ℕ) ≠ (a + 1, b) := by
            intro h; simp only [Prod.mk.injEq] at h; omega
          have hd2 : ((a - 1, b) : ℕ × ℕ) ≠ (a, b + 1) := by
            intro h; simp only [Prod.mk.injEq] at h; omega
          have hd3 : ((a + 1, b) : ℕ × ℕ) ≠ (a, b + 1) := by
            intro h; simp only [Prod.mk.injEq] at h; omega
          have hcard : {((a - 1, b) : ℕ × ℕ), (a + 1, b), (a, b + 1)} ⊆
              (neighbors a b).filter (fun v => ell (mOf (k + 1)) v < 1 + min X Y) := by
            intro v hv
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl | rfl
            · exact Finset.mem_filter.mpr ⟨hmemL, by rw [e1]; omega⟩
            · exact Finset.mem_filter.mpr ⟨hmemR, by rw [e2]; omega⟩
            · exact Finset.mem_filter.mpr ⟨hmemU, by rw [e4]; omega⟩
          have hcard3 : ({((a - 1, b) : ℕ × ℕ), (a + 1, b), (a, b + 1)} :
              Finset (ℕ × ℕ)).card = 3 := by
            first
            | rw [Finset.card_insert_of_notMem (by simp [hd1, hd2]),
                Finset.card_insert_of_notMem (by simp [hd3]), Finset.card_singleton]
            | rw [Finset.card_insert_of_not_mem (by simp [hd1, hd2]),
                Finset.card_insert_of_not_mem (by simp [hd3]), Finset.card_singleton]
          calc (3 : ℕ) = ({((a - 1, b) : ℕ × ℕ), (a + 1, b), (a, b + 1)} :
                Finset (ℕ × ℕ)).card := hcard3.symm
            _ ≤ _ := Finset.card_le_card hcard
      · -- a, b both odd: the hard case
        have hval : ell (mOf (k + 1)) (a, b) = 2 * ell (mOf k) (a / 2, b / 2) := by
          rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
        rw [hval] at hpos ⊢
        have hpos' : 0 < ell (mOf k) (a / 2, b / 2) := by omega
        have hab' : a / 2 + b / 2 ≤ mOf k := by omega
        have key := ih (a / 2) (b / 2) hab' hpos'
        set i := a / 2 with hidef
        set j := b / 2 with hjdef
        have hai : a = 2 * i + 1 := by omega
        have hbj : b = 2 * j + 1 := by omega
        have hLeft : a ≥ 1 → ell (mOf (k + 1)) (a - 1, b) =
            1 + min (2 * ell (mOf k) (i, j)) (2 * ell (mOf k) (i - 1, j)) := by
          intro ha1
          have step : ell (mOf (k + 1)) (a - 1, b) =
              1 + min (2 * ell (mOf k) ((a - 1) / 2 - 1, b / 2)) (2 * ell (mOf k) ((a - 1) / 2, b / 2)) := by
            rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
          rw [step, show (((a - 1) / 2 - 1, b / 2) : ℕ × ℕ) = (i - 1, j) from
                Prod.ext (by omega) (by omega),
              show (((a - 1) / 2, b / 2) : ℕ × ℕ) = (i, j) from Prod.ext (by omega) (by omega)]
          omega
        have hRight : ell (mOf (k + 1)) (a + 1, b) =
            1 + min (2 * ell (mOf k) (i, j)) (2 * ell (mOf k) (i + 1, j)) := by
          have step : ell (mOf (k + 1)) (a + 1, b) =
              1 + min (2 * ell (mOf k) ((a + 1) / 2 - 1, b / 2)) (2 * ell (mOf k) ((a + 1) / 2, b / 2)) := by
            rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
          rw [step, show (((a + 1) / 2 - 1, b / 2) : ℕ × ℕ) = (i, j) from
                Prod.ext (by omega) (by omega),
              show (((a + 1) / 2, b / 2) : ℕ × ℕ) = (i + 1, j) from Prod.ext (by omega) (by omega)]
        have hDown : b ≥ 1 → ell (mOf (k + 1)) (a, b - 1) =
            1 + min (2 * ell (mOf k) (i, j)) (2 * ell (mOf k) (i, j - 1)) := by
          intro hb1
          have step : ell (mOf (k + 1)) (a, b - 1) =
              1 + min (2 * ell (mOf k) (a / 2, (b - 1) / 2 - 1)) (2 * ell (mOf k) (a / 2, (b - 1) / 2)) := by
            rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
          rw [step, show ((a / 2, (b - 1) / 2 - 1) : ℕ × ℕ) = (i, j - 1) from
                Prod.ext (by omega) (by omega),
              show ((a / 2, (b - 1) / 2) : ℕ × ℕ) = (i, j) from Prod.ext (by omega) (by omega)]
          omega
        have hUp : ell (mOf (k + 1)) (a, b + 1) =
            1 + min (2 * ell (mOf k) (i, j)) (2 * ell (mOf k) (i, j + 1)) := by
          have step : ell (mOf (k + 1)) (a, b + 1) =
              1 + min (2 * ell (mOf k) (a / 2, (b + 1) / 2 - 1)) (2 * ell (mOf k) (a / 2, (b + 1) / 2)) := by
            rw [ell]; dsimp only; rw [hm0eq]; split_ifs <;> omega
          rw [step, show ((a / 2, (b + 1) / 2 - 1) : ℕ × ℕ) = (i, j) from
                Prod.ext (by omega) (by omega),
              show ((a / 2, (b + 1) / 2) : ℕ × ℕ) = (i, j + 1) from Prod.ext (by omega) (by omega)]
        set f : ℕ × ℕ → ℕ × ℕ := fun pq =>
          if pq.1 + 1 = i then (a - 1, b)
          else if pq.2 + 1 = j then (a, b - 1)
          else if pq.1 = i + 1 then (a + 1, b)
          else (a, b + 1) with hfdef
        have hf1 : i ≥ 1 → f (i - 1, j) = (a - 1, b) := by
          intro hi1; simp only [hfdef]; split_ifs <;> first | omega | rfl
        have hf2 : j ≥ 1 → f (i, j - 1) = (a, b - 1) := by
          intro hj1; simp only [hfdef]; split_ifs <;> first | omega | rfl
        have hf3 : f (i + 1, j) = (a + 1, b) := by
          simp only [hfdef]; split_ifs <;> first | omega | rfl
        have hf4 : f (i, j + 1) = (a, b + 1) := by
          simp only [hfdef]; split_ifs <;> first | omega | rfl
        have hmaps : ∀ p ∈ (neighbors i j).filter (fun v => ell (mOf k) v < ell (mOf k) (i, j)),
            f p ∈ (neighbors a b).filter
              (fun v => ell (mOf (k + 1)) v < 2 * ell (mOf k) (i, j)) := by
          intro p hp
          simp only [Finset.mem_filter] at hp
          obtain ⟨hp_mem, hp_small⟩ := hp
          rw [mem_neighbors] at hp_mem
          rcases hp_mem with rfl | rfl | ⟨hi1, rfl⟩ | ⟨hj1, rfl⟩
          · rw [hf3, Finset.mem_filter, hRight]
            refine ⟨(mem_neighbors a b _).mpr (Or.inl rfl), ?_⟩
            omega
          · rw [hf4, Finset.mem_filter, hUp]
            refine ⟨(mem_neighbors a b _).mpr (Or.inr (Or.inl rfl)), ?_⟩
            omega
          · have ha1 : a ≥ 1 := by omega
            rw [hf1 hi1, Finset.mem_filter, hLeft ha1]
            refine ⟨(mem_neighbors a b _).mpr (Or.inr (Or.inr (Or.inl ⟨ha1, rfl⟩))), ?_⟩
            omega
          · have hb1 : b ≥ 1 := by omega
            rw [hf2 hj1, Finset.mem_filter, hDown hb1]
            refine ⟨(mem_neighbors a b _).mpr (Or.inr (Or.inr (Or.inr ⟨hb1, rfl⟩))), ?_⟩
            omega
        have hinj : Set.InjOn f ↑((neighbors i j).filter
            (fun v => ell (mOf k) v < ell (mOf k) (i, j))) := by
          intro p hp q hq hpq
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hp hq
          rw [mem_neighbors] at hp hq
          rcases hp.1 with rfl | rfl | ⟨hpi, rfl⟩ | ⟨hpj, rfl⟩ <;>
            rcases hq.1 with rfl | rfl | ⟨hqi, rfl⟩ | ⟨hqj, rfl⟩ <;>
            simp only [hfdef] at hpq <;>
            split_ifs at hpq <;>
            simp only [Prod.mk.injEq] at hpq ⊢ <;>
            omega
        have hsub : ((neighbors i j).filter
              (fun v => ell (mOf k) v < ell (mOf k) (i, j))).image f ⊆
            (neighbors a b).filter (fun v => ell (mOf (k + 1)) v < 2 * ell (mOf k) (i, j)) := by
          intro v hv
          simp only [Finset.mem_image] at hv
          obtain ⟨p, hp, rfl⟩ := hv
          exact hmaps p hp
        calc 3 ≤ ((neighbors i j).filter (fun v => ell (mOf k) v < ell (mOf k) (i, j))).card :=
              key
          _ = (((neighbors i j).filter
                (fun v => ell (mOf k) v < ell (mOf k) (i, j))).image f).card :=
              (Finset.card_image_of_injOn hinj).symm
          _ ≤ ((neighbors a b).filter
                (fun v => ell (mOf (k + 1)) v < 2 * ell (mOf k) (i, j))).card :=
              Finset.card_le_card hsub

end BootstrapPercolation.Lemma1Triangle
