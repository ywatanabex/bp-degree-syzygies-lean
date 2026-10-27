import BPFixedPoints.Incidence.VertexProjectiveTwistFaceRestrictions

/-! # The full original twist face-section diagram in mixed coordinates

The coefficient restriction is defined by the existing refinement and the
inverse of the existing frame unit. Actual sheaf restrictions prove its
identity and composition laws through the specified coordinate maps.
-/

namespace BPFixedPoints.CechProduct
variable {V : Type} [Fintype V] [DecidableEq V] (R : Type) [CommRing R]

/-- Original mixed-coordinate section restriction, using the inverse frame-transition unit. -/
noncomputable def multiTwistFaceRestriction {q r : V → Fin 3} (h : FaceRefines q r) (a : V → ℤ) :
    FaceRing R q →ₗ[R] FaceRing R r :=
  (LinearMap.mulRight R (↑((multiTwistTransition R h a)⁻¹) : FaceRing R r)).comp
    (faceRefinementMap R h).toLinearMap

/-- The coefficient formula uses only the original refinement and frame unit. -/
theorem multiTwistFaceRestriction_apply {q r : V → Fin 3} (h : FaceRefines q r) (a : V → ℤ)
    (x : FaceRing R q) :
    multiTwistFaceRestriction R h a x =
      faceRefinementMap R h x * (↑((multiTwistTransition R h a)⁻¹) : FaceRing R r) := rfl

end BPFixedPoints.CechProduct

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- The specified original face coordinates identify every actual twist restriction with its coefficient map. -/
theorem vertexTwistSheafFaceSections_restrict (a : V → ℤ)
    {q r : V → Fin 3} (h : FaceRefines q r)
    (s : Γ(vertexTwistSheaf R V a, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)) :
    vertexTwistSheafFaceSectionsEquiv R V a r
      ((vertexTwistSheaf R V a).presheaf.map (homOfLE (vertexBinaryFaceOpen_refinement R V h)).op s) =
        multiTwistFaceRestriction R h a (vertexTwistSheafFaceSectionsEquiv R V a q s) :=
  vertexTwistSheafFaceSectionsEquiv_restrict R V a h s

/-- The explicit original coefficient restriction preserves identity. -/
theorem multiTwistFaceRestriction_refl (a : V → ℤ) (q : V → Fin 3) (x : FaceRing R q) :
    multiTwistFaceRestriction R (faceRefines_refl q) a x = x := by
  obtain ⟨s, rfl⟩ := (vertexTwistSheafFaceSectionsEquiv R V a q).surjective x
  rw [← vertexTwistSheafFaceSections_restrict]
  congr 1
  change (vertexTwistSheaf R V a).presheaf.map (𝟙 (op _)) s = s
  simp

/-- Every pair of original coefficient restrictions composes as the original face refinement. -/
theorem multiTwistFaceRestriction_comp (a : V → ℤ) {q r t : V → Fin 3}
    (hqr : FaceRefines q r) (hrt : FaceRefines r t) (x : FaceRing R q) :
    multiTwistFaceRestriction R hrt a (multiTwistFaceRestriction R hqr a x) =
      multiTwistFaceRestriction R (faceRefines_trans hqr hrt) a x := by
  obtain ⟨s, rfl⟩ := (vertexTwistSheafFaceSectionsEquiv R V a q).surjective x
  rw [← vertexTwistSheafFaceSections_restrict, ← vertexTwistSheafFaceSections_restrict,
    ← vertexTwistSheafFaceSections_restrict]
  congr 1
  exact ((vertexTwistSheaf R V a).presheaf.map_comp_apply
    (homOfLE (vertexBinaryFaceOpen_refinement R V hqr)).op
    (homOfLE (vertexBinaryFaceOpen_refinement R V hrt)).op s).symm

noncomputable local instance vertexFaceDiagramHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _

/-- The native degree-zero local Ext restriction is the same original coefficient map. -/
theorem vertexTwistSheafFaceH0LinearEquiv_restrict (a : V → ℤ)
    {q r : V → Fin 3} (h : FaceRefines q r)
    (x : (vertexTwistAbelianSheaf R V a).H' 0 (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)) :
    vertexTwistSheafFaceH0LinearEquiv R V a r
      (((vertexTwistAbelianSheaf R V a).cohomologyPresheaf 0).map
        (homOfLE (vertexBinaryFaceOpen_refinement R V h)).op x) =
      multiTwistFaceRestriction R h a (vertexTwistSheafFaceH0LinearEquiv R V a q x) := by
  change vertexTwistSheafFaceSectionsEquiv R V a r
    (SheafTools.localSheafH0Equiv (vertexTwistAbelianSheaf R V a) _
      (((vertexTwistAbelianSheaf R V a).cohomologyPresheaf 0).map
        (homOfLE (vertexBinaryFaceOpen_refinement R V h)).op x)) = _
  rw [SheafTools.localSheafH0Equiv_naturality]
  exact vertexTwistSheafFaceSections_restrict R V a h _

end BPFixedPoints.ProjectiveLine
