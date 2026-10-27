import BPFixedPoints.Incidence.CechTransitionCocycle

/-! # Transition cocycles for every integral multi-twist

Tensor products, duals and integer powers of the actual homogeneous-coordinate
units give the transition units of all projective line-bundle twists used by
the Koszul-Cech model. This is explicit descent data; constructing the global
line bundles and comparing their derived cohomology is a further step.
-/

namespace BPFixedPoints.CechProduct
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [DecidableEq V] [Fintype V] (R : Type*) [CommRing R]

/-- Explicit transition unit for an arbitrary integral multi-twist. -/
noncomputable def multiTwistTransition {q r : V → Fin 3} (h : FaceRefines q r) (a : V → ℤ) :
    (FaceRing R r)ˣ :=
  ∏ v, faceTransitionUnit R h v ^ a v

/-- Tensor products add multi-twists at the level of the actual transition units. -/
theorem multiTwistTransition_add {q r : V → Fin 3} (h : FaceRefines q r) (a b : V → ℤ) :
    multiTwistTransition R h (a+b) = multiTwistTransition R h a * multiTwistTransition R h b := by
  simp only [multiTwistTransition, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

/-- Dualizing the multi-twist inverts its actual transition unit. -/
theorem multiTwistTransition_neg {q r : V → Fin 3} (h : FaceRefines q r) (a : V → ℤ) :
    multiTwistTransition R h (-a) = (multiTwistTransition R h a)⁻¹ := by
  simp only [multiTwistTransition, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]

/-- Every integral multi-twist satisfies the actual triple-overlap cocycle identity. -/
theorem multiTwistTransition_cocycle {q r s : V → Fin 3}
    (hqr : FaceRefines q r) (hrs : FaceRefines r s) (a : V → ℤ) :
    Units.map (faceRefinementMap R hrs).toMonoidHom (multiTwistTransition R hqr a) *
      multiTwistTransition R hrs a = multiTwistTransition R (faceRefines_trans hqr hrs) a := by
  simp only [multiTwistTransition, map_prod, map_zpow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  rw [← mul_zpow, faceTransitionUnit_cocycle]

end BPFixedPoints.CechProduct
