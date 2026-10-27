import BPFixedPoints.Incidence.CechTwoMiddleProjection
import BPFixedPoints.Incidence.VertexProjectiveTwistTwoH1All

/-! # Original full middle cocycles and actual two-vertex H1 -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct SchemeTools Finsupp TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
variable (R : Type) [CommRing R] [IsNoetherianRing R]
noncomputable local instance twoMiddleCocyclesHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 2))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Apply the original native row connecting maps to the two original row-overlap coefficients. -/
noncomputable def vertexTwistTwoMiddleRowClasses (d : Fin 2 → ℕ) :
    C R (Fin 2) →ₗ[R]
      (vertexTwistRowH1Module R (fun v => -(d v : ℤ)) 0 ×
        vertexTwistRowH1Module R (fun v => -(d v : ℤ)) 1) :=
  ((vertexTwistRowCoefficientH1LinearEquiv R (fun v => -(d v : ℤ)) 0).toLinearMap.comp
    ((Submodule.mkQ _).comp ((LinearMap.proj ![0,2]).comp (faceEquiv R).toLinearMap))).prod
  ((vertexTwistRowCoefficientH1LinearEquiv R (fun v => -(d v : ℤ)) 1).toLinearMap.comp
    ((Submodule.mkQ _).comp ((LinearMap.proj ![1,2]).comp (faceEquiv R).toLinearMap)))

/-- Original rectangular closedness makes the two native row classes match under actual restrictions. -/
theorem vertexTwistTwoMiddleRowClasses_closed (d : Fin 2 → ℕ) (c : twoMiddleCycles R d) :
    schemeBaseSquareCohomologyDifference (vertexToBase R (Fin 2))
      (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) (vertexTwoOuterSquare R) 1
        (vertexTwistTwoMiddleRowClasses R d c.val) = 0 := by
  change vertexTwistRowH1Restriction R (fun v => -(d v : ℤ)) (b := 0) (c := 2) (Or.inr rfl)
    (vertexTwistRowCoefficientH1LinearEquiv R _ 0 (Submodule.Quotient.mk (faceEquiv R c.val ![0,2]))) -
    vertexTwistRowH1Restriction R (fun v => -(d v : ℤ)) (b := 1) (c := 2) (Or.inr rfl)
    (vertexTwistRowCoefficientH1LinearEquiv R _ 1 (Submodule.Quotient.mk (faceEquiv R c.val ![1,2]))) = 0
  rw [← vertexTwistRowCoefficientH1LinearEquiv_restrict,← vertexTwistRowCoefficientH1LinearEquiv_restrict,
    twoRowQuotientRestriction_mk,twoRowQuotientRestriction_mk,← map_sub]
  apply (vertexTwistRowCoefficientH1LinearEquiv R (fun v => -(d v : ℤ)) 2).map_eq_zero_iff.mpr
  change Submodule.Quotient.mk
    (twoRowRestriction R (fun v => -(d v : ℤ)) (b := 0) (c := 2) (Or.inr rfl) 2 (faceEquiv R c.val ![0,2]) -
      twoRowRestriction R (fun v => -(d v : ℤ)) (b := 1) (c := 2) (Or.inr rfl) 2 (faceEquiv R c.val ![1,2])) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨(faceEquiv R c.val ![2,0],faceEquiv R c.val ![2,1]),?_⟩
  have hc := twoMiddleCycles_rectangle_closed R d c
  exact (sub_eq_zero.mp hc).symm

/-- The actual H1 class specified by the original row connecting maps and original native restrictions.
The construction does not use the full state projection or transport the geometric scalar action. -/
noncomputable def vertexTwistTwoMiddleCocyclesToH1 (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    twoMiddleCycles R d →ₗ[R] vertexTwistTwoH1Module R d :=
  (vertexTwistTwoH1RestrictionKernelEquiv R d hd).symm.toLinearMap.comp
    (((vertexTwistTwoMiddleRowClasses R d).comp (twoMiddleCycles R d).subtype).codRestrict _
      (vertexTwistTwoMiddleRowClasses_closed R d))

/-- Each resulting actual class retains both original row connecting classes as its actual native restrictions. -/
theorem vertexTwistTwoMiddleCocyclesToH1_rows (d : Fin 2 → ℕ) (hd : 0 < d 1)
    (c : twoMiddleCycles R d) :
    (vertexTwistTwoH1RestrictionKernelEquiv R d hd (vertexTwistTwoMiddleCocyclesToH1 R d hd c)).val =
      vertexTwistTwoMiddleRowClasses R d c.val := by
  change ((vertexTwistTwoH1RestrictionKernelEquiv R d hd)
    ((vertexTwistTwoH1RestrictionKernelEquiv R d hd).symm _)).val = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Actual row state coordinates of the native comparison equal the original Laurent projections of the cocycle. -/
theorem vertexTwistTwoMiddleCocyclesToH1_rowStates (d : Fin 2 → ℕ) (hd : 0 < d 1)
    (c : twoMiddleCycles R d) :
    (vertexTwistTwoH1StateKernelEquiv R d hd (vertexTwistTwoMiddleCocyclesToH1 R d hd c)).val =
      twoMiddleRowStates R d c.val := by
  change vertexTwistTwoRowH1Coordinates R d
    (vertexTwistTwoH1RestrictionKernelEquiv R d hd (vertexTwistTwoMiddleCocyclesToH1 R d hd c)).val = _
  rw [vertexTwistTwoMiddleCocyclesToH1_rows]
  apply Prod.ext <;> exact vertexTwistRowStateLinearEquiv_representative R d _ _

/-- For every original full degree-one cocycle, the specified actual comparison has exactly its original full contraction projection. -/
theorem vertexTwistTwoMiddleCocyclesToH1_projection (d : Fin 2 → ℕ) (hd : 0 < d 1)
    (c : twoMiddleCycles R d) :
    vertexTwistTwoH1StateEquiv R d (vertexTwistTwoMiddleCocyclesToH1 R d hd c) =
      twoMiddleStateProjection R d c := by
  rw [vertexTwistTwoH1StateEquiv_of_pos R d hd]
  exact twoMiddleRowStates_projection R d hd c _ (vertexTwistTwoMiddleCocyclesToH1_rowStates R d hd c)

end BPFixedPoints.ProjectiveLine
