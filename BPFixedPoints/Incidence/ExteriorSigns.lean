import BPFixedPoints.Incidence.Koszul

/-!
# Shuffle signs for the edge exterior product

Use the existing Koszul convention of ordering finite edge sets increasingly.
Count right-factor edges smaller than each left-factor edge, the inversions
in the concatenation of the two ordered lists.
-/

namespace BPFixedPoints.Koszul

variable {E R : Type*} [LinearOrder E] [CommRing R]

def shuffleIndex (S T : Finset E) : ℕ := ∑ e ∈ S, index T e
def shuffleSign (S T : Finset E) : R := (-1) ^ shuffleIndex S T

@[simp] theorem shuffleIndex_empty_left (T : Finset E) : shuffleIndex ∅ T = 0 := by
  simp [shuffleIndex]
@[simp] theorem shuffleIndex_empty_right (S : Finset E) : shuffleIndex S ∅ = 0 := by
  simp [shuffleIndex, index]

theorem index_union {S T : Finset E} (h : Disjoint S T) (e : E) :
    index (S ∪ T) e = index S e + index T e := by
  unfold index
  rw [Finset.filter_union, Finset.card_union_of_disjoint (h.mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

theorem shuffleIndex_union_left {S T : Finset E} (h : Disjoint S T) (U : Finset E) :
    shuffleIndex (S ∪ T) U = shuffleIndex S U + shuffleIndex T U :=
  Finset.sum_union h

theorem shuffleIndex_union_right (S : Finset E) {T U : Finset E} (h : Disjoint T U) :
    shuffleIndex S (T ∪ U) = shuffleIndex S T + shuffleIndex S U := by
  simp only [shuffleIndex, index_union h, Finset.sum_add_distrib]

theorem shuffleIndex_erase_left {S : Finset E} (T : Finset E) {e : E} (he : e ∈ S) :
    shuffleIndex (S.erase e) T + index T e = shuffleIndex S T := by
  exact Finset.sum_erase_add _ _ he

theorem index_insert (T : Finset E) {e : E} (he : e ∉ T) (s : E) :
    index (Insert.insert e T) s = index T s + if e < s then 1 else 0 := by
  by_cases h : e < s <;> simp [index, Finset.filter_insert, h, he]

theorem shuffleIndex_insert_right (S : Finset E) {T : Finset E} {e : E} (he : e ∉ T) :
    shuffleIndex S (Insert.insert e T) = shuffleIndex S T + (S.filter (e < ·)).card := by
  simp only [shuffleIndex, index_insert T he, Finset.sum_add_distrib]
  congr 1
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem shuffleIndex_erase_right (S : Finset E) {T : Finset E} {e : E} (he : e ∈ T) :
    shuffleIndex S (T.erase e) + (S.filter (e < ·)).card = shuffleIndex S T := by
  rw [← shuffleIndex_insert_right S (Finset.notMem_erase e T), Finset.insert_erase he]

theorem index_add_greater {S : Finset E} {e : E} (he : e ∉ S) :
    index S e + (S.filter (e < ·)).card = S.card := by
  rw [index, ← Finset.card_union_of_disjoint]
  · congr 1
    ext s
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hs, _⟩ | ⟨hs, _⟩) <;> exact hs
    · intro hs
      rcases lt_or_gt_of_ne (show s ≠ e from fun h => he (h ▸ hs)) with h | h
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr ⟨hs, h⟩
  · apply Finset.disjoint_left.mpr
    intro s hs ht
    exact (lt_asymm (Finset.mem_filter.mp hs).2 (Finset.mem_filter.mp ht).2)

@[simp] theorem shuffleSign_empty_left (T : Finset E) : shuffleSign (R := R) ∅ T = 1 := by
  simp [shuffleSign]
@[simp] theorem shuffleSign_empty_right (S : Finset E) : shuffleSign (R := R) S ∅ = 1 := by
  simp [shuffleSign]

theorem shuffleSign_union_left {S T : Finset E} (h : Disjoint S T) (U : Finset E) :
    shuffleSign (R := R) (S ∪ T) U = shuffleSign S U * shuffleSign T U := by
  rw [shuffleSign, shuffleIndex_union_left h, pow_add]; rfl

theorem shuffleSign_union_right (S : Finset E) {T U : Finset E} (h : Disjoint T U) :
    shuffleSign (R := R) S (T ∪ U) = shuffleSign S T * shuffleSign S U := by
  rw [shuffleSign, shuffleIndex_union_right S h, pow_add]; rfl

@[simp] theorem neg_one_pow_mul_self (n : ℕ) : (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
  rw [← mul_pow]; simp

/-- Leibniz sign when removing an edge from the left factor. -/
theorem shuffleSign_erase_left {S T : Finset E} (h : Disjoint S T) {e : E} (he : e ∈ S) :
    shuffleSign (R := R) S T * sign (S ∪ T) e =
      sign S e * shuffleSign (S.erase e) T := by
  unfold shuffleSign sign
  rw [← shuffleIndex_erase_left T he, index_union h, pow_add, pow_add]
  calc
    _ = ((-1 : R) ^ index S e * (-1) ^ shuffleIndex (S.erase e) T) *
        ((-1) ^ index T e * (-1) ^ index T e) := by ring
    _ = _ := by rw [neg_one_pow_mul_self, mul_one]

/-- Leibniz sign when removing an edge from the right factor. -/
theorem shuffleSign_erase_right {S T : Finset E} (h : Disjoint S T) {e : E} (he : e ∈ T) :
    shuffleSign (R := R) S T * sign (S ∪ T) e =
      (-1 : R) ^ S.card * sign T e * shuffleSign S (T.erase e) := by
  have heS : e ∉ S := fun heS => Finset.disjoint_left.mp h heS he
  unfold shuffleSign sign
  rw [← shuffleIndex_erase_right S he, index_union h, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  have hh := index_add_greater heS
  omega

/-- The two terms removing the unique common edge from opposite sides have opposite signs. -/
theorem shuffleSign_overlap_cancel {S T : Finset E} {e : E}
    (heS : e ∈ S) (heT : e ∈ T) :
    sign (A := R) S e * shuffleSign (S.erase e) T =
      -((-1 : R) ^ S.card * sign T e * shuffleSign S (T.erase e)) := by
  have hcard : S.card = (S.erase e).card + 1 := by
    simpa only [Finset.insert_erase heS] using
      (Finset.card_insert_of_notMem (Finset.notMem_erase e S))
  have hl := shuffleIndex_erase_right (S.erase e) heT
  have hr := shuffleIndex_erase_left (T.erase e) heS
  have hs := index_add_greater (Finset.notMem_erase e S)
  unfold sign shuffleSign
  rw [← hl, ← hr, index_erase_self, hcard]
  simp only [pow_add, pow_one]
  rw [index_erase_self] at hs
  have hpow : (-1 : R) ^ index S e * (-1) ^ ((S.erase e).filter (e < ·)).card =
      (-1 : R) ^ (S.erase e).card := by rw [← pow_add, hs]
  calc
    _ = ((-1 : R) ^ index S e * (-1) ^ ((S.erase e).filter (e < ·)).card) *
        (-1) ^ shuffleIndex (S.erase e) (T.erase e) := by ring
    _ = ((-1 : R) ^ (S.erase e).card * (-1) ^ shuffleIndex (S.erase e) (T.erase e)) *
        ((-1) ^ index T e * (-1) ^ index T e) := by rw [hpow, neg_one_pow_mul_self, mul_one]
    _ = _ := by ring

end BPFixedPoints.Koszul
