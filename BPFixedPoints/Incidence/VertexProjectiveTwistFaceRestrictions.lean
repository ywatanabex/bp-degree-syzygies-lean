import BPFixedPoints.Incidence.VertexProjectiveFaceTwistUnits

/-! # Canonical face coordinates of the original twist restrictions

The existing multi-twist unit compares frames. Section coefficients transform
by its inverse; neither the original sheaf nor the original unit is redefined.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CechProduct TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- Canonical coefficients of the actual restriction retain the original frame-transition equation. -/
theorem vertexTwistSheafFaceSectionsEquiv_restrict_mul (a : V → ℤ)
    {q r : V → Fin 3} (h : FaceRefines q r)
    (s : Γ(vertexTwistSheaf R V a, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)) :
    vertexTwistSheafFaceSectionsEquiv R V a r
      ((vertexTwistSheaf R V a).presheaf.map (homOfLE (vertexBinaryFaceOpen_refinement R V h)).op s) *
        (multiTwistTransition R h a : FaceRing R r) =
      faceRefinementMap R h (vertexTwistSheafFaceSectionsEquiv R V a q s) := by
  let t := (vertexTwistSheaf R V a).presheaf.map (homOfLE (vertexBinaryFaceOpen_refinement R V h)).op s
  have ht := vertexTwistSheafChartCoefficient_pair_transition R V a
    (vertexBooleanPivot V (vertexFaceBaseChoice V q)) (vertexBooleanPivot V (vertexFaceBaseChoice V r))
    (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) r) (vertexFaceRefinement_le_pair R V h) t
  have hc := congrArg (vertexFaceSectionsEquiv R V r) ht
  rw [map_mul, vertexFaceRefinement_pair_unit] at hc
  have hs := vertexTwistSheafFaceSectionsWithChartEquiv_restrict R V a (vertexFaceBaseChoice V q)
    (vertexFaceBaseChoice_refines V q) h s
  change vertexTwistSheafFaceSectionsWithChartEquiv R V a (vertexFaceBaseChoice V q) r
    (faceRefines_trans (vertexFaceBaseChoice_refines V q) h) t =
      vertexTwistSheafFaceSectionsEquiv R V a r t * (multiTwistTransition R h a : FaceRing R r) at hc
  exact hc.symm.trans hs

/-- Actual canonical section coefficients restrict by the inverse of the existing frame-transition unit. -/
theorem vertexTwistSheafFaceSectionsEquiv_restrict (a : V → ℤ)
    {q r : V → Fin 3} (h : FaceRefines q r)
    (s : Γ(vertexTwistSheaf R V a, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)) :
    vertexTwistSheafFaceSectionsEquiv R V a r
      ((vertexTwistSheaf R V a).presheaf.map (homOfLE (vertexBinaryFaceOpen_refinement R V h)).op s) =
      faceRefinementMap R h (vertexTwistSheafFaceSectionsEquiv R V a q s) *
        (↑((multiTwistTransition R h a)⁻¹) : FaceRing R r) := by
  have ht := vertexTwistSheafFaceSectionsEquiv_restrict_mul R V a h s
  calc
    _ = (_ * (multiTwistTransition R h a : FaceRing R r)) *
        (↑((multiTwistTransition R h a)⁻¹) : FaceRing R r) := by
      rw [mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [ht]

end BPFixedPoints.ProjectiveLine
