import BPFixedPoints.Incidence.CechZeroDegrees
import BPFixedPoints.Incidence.CechCubicalFaceDifferential

/-! # Original degree-zero twist cocycles and adjacent chart restrictions -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable {V : Type} [Fintype V] [DecidableEq V] (R : Type) [CommRing R]

omit [Fintype V] in
/-- An adjacent original chart refines to the specified one-coordinate overlap. -/
theorem chartOverlapRefines (σ : V → Bool) (v : V) (b : Bool) :
    FaceRefines (chartFace (Function.update σ v b)) (overlapFace σ v) := by
  intro w
  by_cases hw : w = v
  · subst w
    exact Or.inr (overlapFace_self σ v)
  · exact Or.inl (by simp [chartFace,overlapFace,hw])

omit [DecidableEq V] in
/-- The tensor prefix is zero on each original degree-zero chart. -/
theorem faceBoundarySign_chart (σ : V → Bool) (v : V) :
    faceBoundarySign R (chartFace σ) v = if σ v then 1 else -1 := by
  have hp : faceBoundaryPrefix (chartFace σ) v = 0 := by
    unfold faceBoundaryPrefix
    apply Finset.sum_eq_zero
    intro w _
    simp [chartFace_ne_two σ w]
  rw [faceBoundarySign,hp,pow_zero,one_mul]
  cases hv : σ v <;> simp [chartFace,hv]

private theorem chartInsert_d (d : V → ℕ) (σ : V → Bool)
    (x : FaceRing R (chartFace σ)) :
    faceEquiv R ((contraction R d).d (chartInsert R σ x)) =
      ∑ v, Pi.single (overlapFace σ v)
        ((if σ v then (1 : R) else -1) •
          multiTwistFaceRestriction R (faceStep_refines (chartFace σ) v)
            (fun w => -(d w : ℤ)) x) := by
  rw [faceEquiv_d,faceEquiv_chartInsert,cubicalCoefficientD_single]
  apply Finset.sum_congr rfl
  intro v _
  rw [ite_eq_right (chartFace_ne_two σ v),faceBoundarySign_chart]
  rfl

private theorem single_restriction_apply (a : V → ℤ) (p q r : V → Fin 3) (hqr : q = r)
    (hpq : FaceRefines p q) (hpr : FaceRefines p r) (c : R) (x : FaceRing R p) :
    Pi.single q (c • multiTwistFaceRestriction R hpq a x) r =
      c • multiTwistFaceRestriction R hpr a x := by
  subst r
  rw [Pi.single_eq_same]

private theorem chartInsert_d_adjacent (d : V → ℕ) (σ : V → Bool) (v : V) (b : Bool)
    (x : FaceRing R (chartFace (Function.update σ v b))) :
    faceEquiv R ((contraction R d).d (chartInsert R (Function.update σ v b) x)) (overlapFace σ v) =
      (if b then (1 : R) else -1) •
        multiTwistFaceRestriction R (chartOverlapRefines σ v b) (fun w => -(d w : ℤ)) x := by
  rw [chartInsert_d,Finset.sum_apply,Finset.sum_eq_single v]
  · simp only [Function.update_self]
    exact single_restriction_apply R _ _ _ _ (overlapFace_update σ v b) _ _ _ x
  · intro w _ hw
    apply Pi.single_eq_of_ne
    intro h
    exact hw (overlapFace_vertex_eq h).symm
  · simp

private theorem chartInsert_d_nonadjacent (d : V → ℕ) (σ τ : V → Bool) (v : V)
    (hτ : ∀ b, τ ≠ Function.update σ v b) (x : FaceRing R (chartFace τ)) :
    faceEquiv R ((contraction R d).d (chartInsert R τ x)) (overlapFace σ v) = 0 := by
  rw [chartInsert_d,Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro w _
  apply Pi.single_eq_of_ne
  intro he
  have hw : v = w := overlapFace_vertex_eq he
  subst w
  exact hτ (τ v) (overlapFace_source_eq he.symm)

/-- The original differential on every nonpositive twist is precisely the original adjacent restriction difference. -/
theorem faceEquiv_d_zeroCharts_twist (d : V → ℕ) (σ : V → Bool) (v : V)
    (x : (τ : V → Bool) → FaceRing R (chartFace τ)) :
    faceEquiv R ((contraction R d).d (zeroCharts R x)) (overlapFace σ v) =
      multiTwistFaceRestriction R (chartOverlapRefines σ v true) (fun w => -(d w : ℤ))
        (x (Function.update σ v true)) -
      multiTwistFaceRestriction R (chartOverlapRefines σ v false) (fun w => -(d w : ℤ))
        (x (Function.update σ v false)) := by
  classical
  rw [zeroCharts_apply,map_sum,map_sum,Finset.sum_apply]
  have hne : Function.update σ v true ≠ Function.update σ v false := by
    intro h
    have hh := congrFun h v
    simp at hh
  rw [← Finset.sum_subset (Finset.subset_univ
    ({Function.update σ v false,Function.update σ v true} : Finset (V → Bool))) ?_]
  · rw [Finset.sum_pair hne.symm,chartInsert_d_adjacent,chartInsert_d_adjacent]
    simp [sub_eq_add_neg,add_comm]
  · intro τ _ hτ
    apply chartInsert_d_nonadjacent
    intro b
    cases b <;> intro he <;> simp [he] at hτ

/-- A family of original chart coefficients is a cocycle exactly when all original adjacent restrictions agree. -/
theorem zeroCharts_closed_iff (d : V → ℕ)
    (x : (τ : V → Bool) → FaceRing R (chartFace τ)) :
    (contraction R d).d (zeroCharts R x) = 0 ↔
      ∀ (σ : V → Bool) (v : V),
        multiTwistFaceRestriction R (chartOverlapRefines σ v true) (fun w => -(d w : ℤ))
          (x (Function.update σ v true)) =
        multiTwistFaceRestriction R (chartOverlapRefines σ v false) (fun w => -(d w : ℤ))
          (x (Function.update σ v false)) := by
  constructor
  · intro hx σ v
    have he := congrArg (fun c => faceEquiv R c (overlapFace σ v)) hx
    rw [faceEquiv_d_zeroCharts_twist,map_zero,Pi.zero_apply,sub_eq_zero] at he
    exact he
  · intro hx
    apply (faceEquiv R).injective
    funext q
    by_cases hq : faceDegree q = 1
    · obtain ⟨σ,v,rfl⟩ := (faceDegree_eq_one_iff q).mp hq
      rw [faceEquiv_d_zeroCharts_twist,hx,sub_self,map_zero,Pi.zero_apply]
    · rw [map_zero,Pi.zero_apply]
      apply faceEquiv_eq_zero_of_degree R
        (contraction_d_degree R d 0 _ (zeroCharts_mem_supported R x))
      exact_mod_cast hq

end BPFixedPoints.CechProduct
