import BPFixedPoints.Incidence.VertexProjectiveTwistTwoH2States
import BPFixedPoints.Incidence.CechMinusTwoBasis

/-! # The specified original Laurent generator of actual two-vertex H2 -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Finsupp TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000
variable (R : Type) [CommRing R] [IsNoetherianRing R]
noncomputable local instance vertexTwoH2GeneratorHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 2))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The original double connecting class of the Laurent gap monomial maps to its original scalar. -/
theorem vertexTwistTwoH2_minus_two_representative (r : R) :
    vertexTwistTwoH2_minus_two R
      (vertexTwistTwoCoefficientH2LinearEquiv R (fun _ => -2)
        (Submodule.Quotient.mk (AddMonoidAlgebra.single twoGapExponent r))) = r := by
  let e : H R (fun _ : Fin 2 => 2) ≃ₗ[R] R :=
    (Finsupp.mapDomain.linearEquiv R R
      (Equiv.piCongrRight fun _ : Fin 2 => finCongr phi_two)).trans
        (Finsupp.uniqueLinearEquiv R R (fun _ : Fin 2 => (0 : Fin 1)))
  have hs := (vertexTwistTwoH2StateLinearEquiv_representative R (fun _ => 2)
    (by intro v; decide) (AddMonoidAlgebra.single twoGapExponent r)).trans
      (twoTopStateProjection_gap R r)
  calc
    _ = e (single (fun _ => gapZero) r) := congrArg e hs
    _ = r := by
      change Finsupp.uniqueLinearEquiv R R _ (mapDomain _ (single (fun _ => gapZero) r)) = r
      rw [mapDomain_single]
      simp [Finsupp.uniqueLinearEquiv]

/-- Every actual H2 class is the double connecting class of its scalar Laurent gap representative. -/
theorem vertexTwistTwoH2_minus_two_inverse (r : R) :
    (vertexTwistTwoH2_minus_two R).symm r =
      vertexTwistTwoCoefficientH2LinearEquiv R (fun _ => -2)
        (Submodule.Quotient.mk (AddMonoidAlgebra.single twoGapExponent r)) := by
  apply (vertexTwistTwoH2_minus_two R).injective
  rw [LinearEquiv.apply_symm_apply,vertexTwistTwoH2_minus_two_representative]

end BPFixedPoints.ProjectiveLine
