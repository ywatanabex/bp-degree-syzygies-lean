import BPFixedPoints.Incidence.CechCubicalFaceDifferential

/-! # Original coefficient restrictions in the specified two-direction top boundary -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000
variable (R : Type) [CommRing R]

/-- The original full two-coordinate overlap. -/
abbrev twoTopFace : Fin 2 → Fin 3 := ![2,2]

/-- Every original two-coordinate face refines to the original full overlap. -/
theorem twoFaceRefinesTop (q : Fin 2 → Fin 3) : FaceRefines q twoTopFace := by
  intro v
  right
  fin_cases v <;> rfl

/-- The four original one-overlap coefficient modules, in the specified rectangular order. -/
abbrev TwoRectangleCoefficients :=
  (FaceRing R (![0,2] : Fin 2 → Fin 3) × FaceRing R (![1,2] : Fin 2 → Fin 3)) ×
    (FaceRing R (![2,0] : Fin 2 → Fin 3) × FaceRing R (![2,1] : Fin 2 → Fin 3))

/-- First-direction left minus right, minus second-direction left minus right, using original twist restrictions. -/
noncomputable def twoRectangleBoundary (a : Fin 2 → ℤ) :
    TwoRectangleCoefficients R →ₗ[R] FaceRing R twoTopFace :=
  { toFun := fun x =>
      (multiTwistFaceRestriction R (twoFaceRefinesTop ![0,2]) a x.1.1 -
        multiTwistFaceRestriction R (twoFaceRefinesTop ![1,2]) a x.1.2) -
      (multiTwistFaceRestriction R (twoFaceRefinesTop ![2,0]) a x.2.1 -
        multiTwistFaceRestriction R (twoFaceRefinesTop ![2,1]) a x.2.2)
    map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
    map_smul' := by intros; simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_sub, RingHom.id_apply] }

end BPFixedPoints.CechProduct
