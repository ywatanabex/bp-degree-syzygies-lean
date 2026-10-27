import BPFixedPoints.Incidence.ExteriorSigns
import BPFixedPoints.Incidence.KoszulLinear

/-!
# Exterior products on finite edge sets and the existing Koszul differential

Products of exterior basis states with a common edge vanish; disjoint states
multiply to their union with shuffle sign. Prove the existing edge-removal
operator is an antiderivation for this product.
-/

namespace BPFixedPoints.Koszul

open Finsupp

variable {E R W : Type*} [LinearOrder E] [CommRing R]
  [AddCommGroup W] [Module R W]

noncomputable def wedgeSingle (S T : Finset E) : W →ₗ[R] Space E W :=
  if Disjoint S T then shuffleSign (R := R) S T • Finsupp.lsingle (S ∪ T) else 0

theorem wedgeSingle_apply (S T : Finset E) (w : W) :
    wedgeSingle (R := R) S T w =
      if Disjoint S T then single (S ∪ T) (shuffleSign (R := R) S T • w) else 0 := by
  classical
  simp only [wedgeSingle]
  split_ifs <;> simp [Finsupp.smul_single]

@[simp] theorem wedgeSingle_empty_left (T : Finset E) (w : W) :
    wedgeSingle (R := R) ∅ T w = single T w := by simp [wedgeSingle_apply]
@[simp] theorem wedgeSingle_empty_right (S : Finset E) (w : W) :
    wedgeSingle (R := R) S ∅ w = single S w := by simp [wedgeSingle_apply]

theorem disjoint_erase_left_iff_erase_right {S T : Finset E} (e : E) :
    Disjoint (S.erase e) T ↔ Disjoint S (T.erase e) := by
  simp only [Finset.disjoint_left, Finset.mem_erase]
  aesop

theorem erase_union_left {S T : Finset E} {e : E} (he : e ∉ T) :
    (S ∪ T).erase e = S.erase e ∪ T := by
  ext x
  by_cases hx : x = e <;> simp [hx, he]

theorem erase_union_right {S T : Finset E} {e : E} (he : e ∉ S) :
    (S ∪ T).erase e = S ∪ T.erase e := by
  ext x
  by_cases hx : x = e <;> simp [hx, he]

/-- Leibniz rule for removing one edge from an exterior product, with arbitrary coefficient module. -/
theorem erase_wedgeSingle (e : E) (S T : Finset E) (w : W) :
    linearTerm (R := R) e (LinearMap.id : W →ₗ[R] W) (wedgeSingle (R := R) S T w) =
      (if e ∈ S then sign (A := R) S e • wedgeSingle (R := R) (S.erase e) T w else 0) +
      (if e ∈ T then ((-1 : R) ^ S.card * sign T e) • wedgeSingle (R := R) S (T.erase e) w else 0) := by
  classical
  by_cases h : Disjoint S T
  · have hS : Disjoint (S.erase e) T := h.mono (Finset.erase_subset _ _) le_rfl
    have hT : Disjoint S (T.erase e) := h.mono le_rfl (Finset.erase_subset _ _)
    by_cases heS : e ∈ S
    · have heT : e ∉ T := fun ht => Finset.disjoint_left.mp h heS ht
      simp only [wedgeSingle_apply, h, hS, hT, ↓reduceIte, linearTerm_single,
        Finset.mem_union, heS, heT, true_or, ↓reduceIte, add_zero, LinearMap.id_apply,
        Finsupp.smul_single, smul_smul, erase_union_left heT]
      congr 1
      rw [mul_comm (sign (A := R) (S ∪ T) e), shuffleSign_erase_left h heS]
    · by_cases heT : e ∈ T
      · simp only [wedgeSingle_apply, h, hS, hT, ↓reduceIte, linearTerm_single,
          Finset.mem_union, heS, heT, false_or, ↓reduceIte, zero_add, LinearMap.id_apply,
          Finsupp.smul_single, smul_smul, erase_union_right heS]
        congr 1
        rw [mul_comm (sign (A := R) (S ∪ T) e), shuffleSign_erase_right h heT]
      · simp [wedgeSingle_apply, h, heS, heT]
  · by_cases hS : Disjoint (S.erase e) T
    · have heS : e ∈ S := by
        by_contra he
        exact h (by simpa [Finset.erase_eq_of_notMem he] using hS)
      have heT : e ∈ T := by
        by_contra he
        apply h
        exact Finset.disjoint_left.mpr fun x hx ht =>
          Finset.disjoint_left.mp hS (Finset.mem_erase.mpr ⟨fun heq => he (heq ▸ ht), hx⟩) ht
      have hT := (disjoint_erase_left_iff_erase_right e).mp hS
      have hU₁ : S.erase e ∪ T = S ∪ T := by
        ext x; by_cases hx : x = e <;> simp [hx, heS, heT]
      have hU₂ : S ∪ T.erase e = S ∪ T := by
        ext x; by_cases hx : x = e <;> simp [hx, heS, heT]
      simp only [wedgeSingle_apply, h, hS, hT, heS, heT, ↓reduceIte, map_zero,
        Finsupp.smul_single, smul_smul, hU₁, hU₂, ← Finsupp.single_add]
      rw [shuffleSign_overlap_cancel heS heT, neg_smul, neg_add_cancel, Finsupp.single_zero]
    · have hT : ¬Disjoint S (T.erase e) := by
        simpa only [← disjoint_erase_left_iff_erase_right e] using hS
      simp [wedgeSingle_apply, h, hS, hT]

theorem linearTerm_wedgeSingle (e : E) (f : Module.End R W) (S T : Finset E) (w : W) :
    linearTerm e f (wedgeSingle (R := R) S T w) =
      linearTerm (R := R) e (LinearMap.id : W →ₗ[R] W) (wedgeSingle (R := R) S T (f w)) := by
  classical
  by_cases h : Disjoint S T <;> by_cases he : e ∈ S ∪ T <;>
    simp [wedgeSingle_apply, h, he, map_smul]

/-- Bilinear product in the increasing basis of the standard exterior algebra. -/
noncomputable def wedge : Space E R →ₗ[R] Space E R →ₗ[R] Space E R :=
  Finsupp.llift _ R R _ fun S => Finsupp.llift _ R R _ fun T => wedgeSingle (R := R) S T 1

theorem wedge_single (S T : Finset E) (r s : R) :
    wedge (single S r) (single T s) = wedgeSingle (R := R) S T (r * s) := by
  simp [wedge, wedgeSingle_apply, Finsupp.smul_single, mul_comm, mul_left_comm, mul_assoc]

end BPFixedPoints.Koszul
