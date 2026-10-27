import BPFixedPoints.Incidence.CechTwistZeroCocycles
import BPFixedPoints.Incidence.CechRefinementLocalization

/-! # Original twist chart matching from degree-zero cocycles -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 600000
variable {V : Type} [Fintype V] [DecidableEq V] (R : Type) [CommRing R]

/-- The original common overlap in all vertex directions. -/
abbrev fullOverlapFace : V → Fin 3 := fun _ => 2

omit [Fintype V] [DecidableEq V] in
/-- Every original face refines to the original full overlap. -/
theorem faceRefines_full (q : V → Fin 3) : FaceRefines q fullOverlapFace := fun _ => Or.inr rfl

/-- Multiplication by the original transition unit preserves injectivity of the original refinement. -/
theorem multiTwistFaceRestriction_injective {q r : V → Fin 3} (h : FaceRefines q r) (a : V → ℤ) :
    Function.Injective (multiTwistFaceRestriction R h a) := by
  intro x y he
  apply faceRefinement_injective R h
  have hh := congrArg (fun z : FaceRing R r => z * (multiTwistTransition R h a : FaceRing R r)) he
  simpa only [multiTwistFaceRestriction_apply,mul_assoc,Units.inv_mul,mul_one] using hh

private theorem bool_cube_constant {M : Type*} (f : (V → Bool) → M)
    (hf : ∀ σ v, f (Function.update σ v true) = f (Function.update σ v false)) :
    ∀ σ τ, f σ = f τ := by
  intro σ τ
  have hu (s : V → Bool) (v : V) (b : Bool) : f (Function.update s v b) = f s := by
    have hb (c : Bool) : f (Function.update s v c) = f (Function.update s v false) := by
      cases c
      · rfl
      · exact hf s v
    exact (hb b).trans (by simpa only [Function.update_eq_self] using (hb (s v)).symm)
  let mix (s : Finset V) : V → Bool := fun v => if v ∈ s then τ v else σ v
  have hm (s : Finset V) : f (mix s) = f σ := by
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | @insert v s hv ih =>
      have he : mix (insert v s) = Function.update (mix s) v (τ v) := by
        funext w
        by_cases hw : w = v <;> simp [mix,hw]
      rw [he,hu,ih]
  simpa [mix] using (hm Finset.univ).symm

/-- A degree-zero cocycle has a single common full-overlap value in the original frames. -/
theorem zeroCharts_closed_full (d : V → ℕ)
    (x : (σ : V → Bool) → FaceRing R (chartFace σ))
    (hx : (contraction R d).d (zeroCharts R x) = 0) (σ τ : V → Bool) :
    multiTwistFaceRestriction R (faceRefines_full (chartFace σ)) (fun w => -(d w : ℤ)) (x σ) =
      multiTwistFaceRestriction R (faceRefines_full (chartFace τ)) (fun w => -(d w : ℤ)) (x τ) := by
  apply bool_cube_constant (fun s =>
    multiTwistFaceRestriction R (faceRefines_full (chartFace s)) (fun w => -(d w : ℤ)) (x s)) _ σ τ
  intro s v
  have he := congrArg (multiTwistFaceRestriction R (faceRefines_full (overlapFace s v))
    (fun w => -(d w : ℤ))) ((zeroCharts_closed_iff R d x).mp hx s v)
  simpa only [ProjectiveLine.multiTwistFaceRestriction_comp] using he

/-- Agreement on the full overlap gives the original adjacent matching equations. -/
theorem zeroCharts_closed_of_full (d : V → ℕ)
    (x : (σ : V → Bool) → FaceRing R (chartFace σ))
    (hx : ∀ σ τ,
      multiTwistFaceRestriction R (faceRefines_full (chartFace σ)) (fun w => -(d w : ℤ)) (x σ) =
        multiTwistFaceRestriction R (faceRefines_full (chartFace τ)) (fun w => -(d w : ℤ)) (x τ)) :
    (contraction R d).d (zeroCharts R x) = 0 := by
  apply (zeroCharts_closed_iff R d x).mpr
  intro σ v
  apply multiTwistFaceRestriction_injective R (faceRefines_full (overlapFace σ v))
    (fun w => -(d w : ℤ))
  simpa only [ProjectiveLine.multiTwistFaceRestriction_comp] using
    hx (Function.update σ v true) (Function.update σ v false)

/-- Every degree-zero cocycle satisfies the original restrictions on every pairwise chart intersection. -/
theorem zeroCharts_closed_pair (d : V → ℕ)
    (x : (σ : V → Bool) → FaceRing R (chartFace σ))
    (hx : (contraction R d).d (zeroCharts R x) = 0) (σ τ : V → Bool) :
    multiTwistFaceRestriction R (faceRefines_join_left (chartFace σ) (chartFace τ))
      (fun w => -(d w : ℤ)) (x σ) =
    multiTwistFaceRestriction R (faceRefines_join_right (chartFace σ) (chartFace τ))
      (fun w => -(d w : ℤ)) (x τ) := by
  apply multiTwistFaceRestriction_injective R
    (faceRefines_full (faceJoin (chartFace σ) (chartFace τ))) (fun w => -(d w : ℤ))
  simpa only [ProjectiveLine.multiTwistFaceRestriction_comp] using zeroCharts_closed_full R d x hx σ τ

end BPFixedPoints.CechProduct
