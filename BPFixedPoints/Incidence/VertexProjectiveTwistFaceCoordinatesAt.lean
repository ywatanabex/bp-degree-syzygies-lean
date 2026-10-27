import BPFixedPoints.Incidence.VertexProjectiveTwistFaceDiagram
import BPFixedPoints.Incidence.SchemeModuleOpenRestrictions

/-! # Original twist coordinates on equal presentations of the original face opens -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- The specified original face coordinates on any equal presentation of that same open. -/
noncomputable def vertexTwistFaceSectionsAt (a : V → ℤ) (q : V → Fin 3)
    (U : (vertexScheme R V).Opens)
    (hU : U = SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q) :
    SchemeTools.schemeBaseOpenSectionModule (vertexToBase R V) (vertexTwistSheaf R V a) U ≃ₗ[R]
      FaceRing R q := by
  subst U
  exact vertexTwistSheafFaceSectionsEquiv R V a q

/-- The specified coordinates retain every native restriction between those original opens. -/
theorem vertexTwistFaceSectionsAt_restrict (a : V → ℤ) {q r : V → Fin 3} (h : FaceRefines q r)
    (U W : (vertexScheme R V).Opens)
    (hU : U = SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)
    (hW : W = SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) r) (hWU : W ≤ U)
    (s : SchemeTools.schemeBaseOpenSectionModule (vertexToBase R V) (vertexTwistSheaf R V a) U) :
    vertexTwistFaceSectionsAt R V a r W hW
      (SchemeTools.schemeBaseOpenRestrictionLinear (vertexToBase R V) (vertexTwistSheaf R V a)
        (homOfLE hWU) s) =
      multiTwistFaceRestriction R h a (vertexTwistFaceSectionsAt R V a q U hU s) := by
  subst U
  subst W
  exact vertexTwistSheafFaceSections_restrict R V a h s

end BPFixedPoints.ProjectiveLine
