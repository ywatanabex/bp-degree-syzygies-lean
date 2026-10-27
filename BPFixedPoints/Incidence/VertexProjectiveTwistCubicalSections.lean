import BPFixedPoints.Incidence.CechCubicalFaceDifferential
import BPFixedPoints.Incidence.SchemeModuleOpenRestrictions
import BPFixedPoints.Incidence.VertexProjectiveTwistFaceDifferences

/-! # The cubical complex of actual twist sections and its original coordinates

The differential is a signed sum of native sheaf restrictions with the native
left-minus-right convention. Coefficients use the original geometric base action.
The comparison with the original right-minus-left tensor complex is proved later.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- Actual sections on each original rectangular face, with the original geometric action. -/
noncomputable def vertexTwistCubicalFace (a : V → ℤ) (q : V → Fin 3) : ModuleCat R :=
  SchemeTools.schemeBaseOpenSectionModule (vertexToBase R V) (vertexTwistSheaf R V a)
    (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)

/-- Actual cubical cochains, including all original faces and all overlap degrees. -/
abbrev VertexTwistCubicalSections (a : V → ℤ) := (q : V → Fin 3) → vertexTwistCubicalFace R V a q

/-- Original face frames give the unsigned coordinate equivalence on actual cochains. -/
noncomputable def vertexTwistCubicalCoordinates (a : V → ℤ) :
    VertexTwistCubicalSections R V a ≃ₗ[R] ((q : V → Fin 3) → FaceRing R q) :=
  LinearEquiv.piCongrRight fun q => vertexTwistSheafFaceSectionsEquiv R V a q

/-- The native restriction between the original face section modules. -/
noncomputable def vertexTwistCubicalRestriction (a : V → ℤ) {q r : V → Fin 3}
    (h : FaceRefines q r) : vertexTwistCubicalFace R V a q →ₗ[R] vertexTwistCubicalFace R V a r :=
  SchemeTools.schemeBaseOpenRestrictionLinear (vertexToBase R V) (vertexTwistSheaf R V a)
    (homOfLE (vertexBinaryFaceOpen_refinement R V h))

/-- A native cubical edge uses the actual restriction and the native left-minus-right sign. -/
noncomputable def vertexTwistCubicalEdge (a : V → ℤ) (q : V → Fin 3) (v : V) :
    Module.End R (VertexTwistCubicalSections R V a) :=
  if q v = 2 then 0 else
    (-faceBoundarySign R q v) •
      ((LinearMap.single R (fun r => vertexTwistCubicalFace R V a r) (faceStep q v)).comp
        ((vertexTwistCubicalRestriction R V a (faceStep_refines q v)).comp (LinearMap.proj q)))

/-- Independently defined native differential: the signed sum of actual open restrictions. -/
noncomputable def vertexTwistCubicalD (a : V → ℤ) :
    Module.End R (VertexTwistCubicalSections R V a) :=
  ∑ q, ∑ v, vertexTwistCubicalEdge R V a q v

/-- Every unsigned edge comparison retains the specified frames, restrictions and opposite difference conventions. -/
theorem vertexTwistCubicalCoordinates_edge (a : V → ℤ) (q : V → Fin 3) (v : V)
    (x : VertexTwistCubicalSections R V a) :
    vertexTwistCubicalCoordinates R V a (vertexTwistCubicalEdge R V a q v x) =
      -cubicalCoefficientEdge R a q v (vertexTwistCubicalCoordinates R V a x) := by
  by_cases hv : q v = 2
  · simp [vertexTwistCubicalEdge, cubicalCoefficientEdge, hv]
  · have he : vertexTwistCubicalCoordinates R V a
        (Pi.single (faceStep q v)
          (vertexTwistCubicalRestriction R V a (faceStep_refines q v) (x q))) =
        Pi.single (faceStep q v)
          (multiTwistFaceRestriction R (faceStep_refines q v) a
            (vertexTwistCubicalCoordinates R V a x q)) := by
      funext r
      by_cases hr : r = faceStep q v
      · subst r
        simp only [vertexTwistCubicalCoordinates, LinearEquiv.piCongrRight_apply,
          Pi.single_eq_same]
        exact vertexTwistSheafFaceSections_restrict R V a (faceStep_refines q v) (x q)
      · simp [vertexTwistCubicalCoordinates, hr]
    simp only [vertexTwistCubicalEdge, cubicalCoefficientEdge, hv, ite_false,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply]
    rw [map_smul, he, neg_smul]

/-- In every degree the unsigned original coordinates anticommute with the two specified differentials. -/
theorem vertexTwistCubicalCoordinates_d (a : V → ℤ) (x : VertexTwistCubicalSections R V a) :
    vertexTwistCubicalCoordinates R V a (vertexTwistCubicalD R V a x) =
      -cubicalCoefficientD R a (vertexTwistCubicalCoordinates R V a x) := by
  simp only [vertexTwistCubicalD, cubicalCoefficientD, LinearMap.sum_apply, map_sum,
    vertexTwistCubicalCoordinates_edge, Finset.sum_neg_distrib]

end BPFixedPoints.ProjectiveLine
