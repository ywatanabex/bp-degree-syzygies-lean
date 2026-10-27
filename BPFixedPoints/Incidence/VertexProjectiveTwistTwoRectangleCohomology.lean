import BPFixedPoints.Incidence.SchemeModuleRectangleLinear
import BPFixedPoints.Incidence.VertexProjectiveTwistTopQuotient

/-! # Actual two-vertex twist H2 from the original signed rectangular sections

All local vanishing hypotheses of the two-direction comparison are supplied
by the original affine faces and the established one-direction degree bound.
The source quotient uses actual sections and native restrictions, for every
integral multi-twist. Its further comparison with coefficient states is separate.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CechProduct TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
variable (R : Type) [CommRing R]
noncomputable local instance vertexTwoRectangleHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 2))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The original two-coordinate face is exactly the intersection of its two original factors. -/
theorem vertexTwoFaceOpen_eq (b c : Fin 3) :
    SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R (Fin 2)) ![b,c] =
      SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b ⊓
        SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 1) c := by
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (iInf_le _ 1)
  · refine le_iInf fun v => ?_
    fin_cases v
    · exact inf_le_left
    · exact inf_le_right

variable [IsNoetherianRing R]

/-- Positive actual local cohomology vanishes on every original two-coordinate rectangle. -/
theorem vertexTwistTwoFace_cohomology_eq_zero (a : Fin 2 → ℤ) (b c : Fin 3) (n : ℕ)
    (x : (vertexTwistAbelianSheaf R (Fin 2) a).H' (n+1)
      (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b ⊓
        SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 1) c)) : x = 0 := by
  revert x
  rw [← vertexTwoFaceOpen_eq]
  intro x
  exact SheafTools.quasicoherent_affineOpen_local_cohomology_eq_zero _ _
    (vertexBinaryFaceOpen_isAffine R (Fin 2) ![b,c]) (vertexTwistSheaf R (Fin 2) a) n x

/-- All affine rectangle groups needed by the specified iterated connecting map vanish. -/
theorem vertexTwistTwoFace_subsingleton (a : Fin 2 → ℤ) (b c : Fin 3) (n : ℕ) :
    Subsingleton ((vertexTwistAbelianSheaf R (Fin 2) a).H' (n+1)
      (SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 0) b ⊓
        SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R (Fin 2) 1) c)) :=
  subsingleton_of_forall_eq 0 (vertexTwistTwoFace_cohomology_eq_zero R a b c n)

/-- The source of the actual top comparison is the quotient by the four native signed face restrictions. -/
abbrev VertexTwistTwoRectangleQuotient (a : Fin 2 → ℤ) :=
  (SchemeTools.schemeBaseOpenSectionModule (vertexToBase R (Fin 2)) (vertexTwistSheaf R (Fin 2) a)
    ((vertexCoordinateOpen R (Fin 2) 0 0 ⊓ vertexCoordinateOpen R (Fin 2) 0 1) ⊓
      (vertexCoordinateOpen R (Fin 2) 1 0 ⊓ vertexCoordinateOpen R (Fin 2) 1 1))) ⧸
    LinearMap.range (SchemeTools.schemeRectangleBoundaryLinear
      (vertexToBase R (Fin 2)) (vertexTwistSheaf R (Fin 2) a)
      (vertexCoordinateOpen R (Fin 2) 1 0) (vertexCoordinateOpen R (Fin 2) 1 1)
      (vertexCoordinateOpen R (Fin 2) 0 0) (vertexCoordinateOpen R (Fin 2) 0 1))

/-- Native signed rectangular sections compute actual global H2, linearly for the original geometric base action. -/
noncomputable def vertexTwistTwoRectangleH2LinearEquiv (a : Fin 2 → ℤ) :
    letI : Module R ((vertexTwistAbelianSheaf R (Fin 2) a).H 2) :=
      SchemeTools.schemeBaseCohomologyModule (vertexToBase R (Fin 2)) (vertexTwistSheaf R (Fin 2) a) 2
    VertexTwistTwoRectangleQuotient R a ≃ₗ[R] (vertexTwistAbelianSheaf R (Fin 2) a).H 2 := by
  letI : Module R ((vertexTwistAbelianSheaf R (Fin 2) a).H 2) :=
    SchemeTools.schemeBaseCohomologyModule (vertexToBase R (Fin 2)) (vertexTwistSheaf R (Fin 2) a) 2
  let A := vertexCoordinateOpen R (Fin 2) 0 0
  let B := vertexCoordinateOpen R (Fin 2) 0 1
  let C := vertexCoordinateOpen R (Fin 2) 1 0
  let D := vertexCoordinateOpen R (Fin 2) 1 1
  let F := (SheafOfModules.toSheaf (vertexScheme R (Fin 2)).ringCatSheaf).obj (vertexTwistSheaf R (Fin 2) a)
  let : Subsingleton (F.H' 1 (vertexCoordinateOpen R (Fin 2) 0 0 ⊓ vertexCoordinateOpen R (Fin 2) 1 0)) := vertexTwistTwoFace_subsingleton R a 0 0 0
  let : Subsingleton (F.H' 1 (vertexCoordinateOpen R (Fin 2) 0 0 ⊓ vertexCoordinateOpen R (Fin 2) 1 1)) := vertexTwistTwoFace_subsingleton R a 0 1 0
  let : Subsingleton (F.H' 1 (vertexCoordinateOpen R (Fin 2) 0 1 ⊓ vertexCoordinateOpen R (Fin 2) 1 0)) := vertexTwistTwoFace_subsingleton R a 1 0 0
  let : Subsingleton (F.H' 1 (vertexCoordinateOpen R (Fin 2) 0 1 ⊓ vertexCoordinateOpen R (Fin 2) 1 1)) := vertexTwistTwoFace_subsingleton R a 1 1 0
  let : Subsingleton (F.H' 1 ((vertexCoordinateOpen R (Fin 2) 0 0 ⊓ vertexCoordinateOpen R (Fin 2) 0 1) ⊓ vertexCoordinateOpen R (Fin 2) 1 0)) := vertexTwistTwoFace_subsingleton R a 2 0 0
  let : Subsingleton (F.H' 1 ((vertexCoordinateOpen R (Fin 2) 0 0 ⊓ vertexCoordinateOpen R (Fin 2) 0 1) ⊓ vertexCoordinateOpen R (Fin 2) 1 1)) := vertexTwistTwoFace_subsingleton R a 2 1 0
  let : Subsingleton (F.H' 2 (vertexCoordinateOpen R (Fin 2) 0 0)) := subsingleton_of_forall_eq 0
    (vertexTwistSheaf_firstOpen_higher_eq_zero R 1 a 0 0)
  let : Subsingleton (F.H' 2 (vertexCoordinateOpen R (Fin 2) 0 1)) := subsingleton_of_forall_eq 0
    (vertexTwistSheaf_firstOpen_higher_eq_zero R 1 a 1 0)
  exact (SchemeTools.schemeRectangleSectionH2LinearEquiv (vertexToBase R (Fin 2))
    (vertexTwistSheaf R (Fin 2) a) C D (vertexCoordinateOpen_cover R (Fin 2) 1) A B).trans
      (SchemeTools.schemeBaseCoverCohomologyLinearEquiv (vertexToBase R (Fin 2))
        (vertexTwistSheaf R (Fin 2) a) (A ⊔ B) (vertexCoordinateOpen_cover R (Fin 2) 0) 2)

/-- Every representative retains the specified original row connecting class followed by the global connecting class. -/
theorem vertexTwistTwoRectangleH2LinearEquiv_mk (a : Fin 2 → ℤ)
    (x : SchemeTools.schemeBaseOpenSectionModule (vertexToBase R (Fin 2)) (vertexTwistSheaf R (Fin 2) a)
      ((vertexCoordinateOpen R (Fin 2) 0 0 ⊓ vertexCoordinateOpen R (Fin 2) 0 1) ⊓
        (vertexCoordinateOpen R (Fin 2) 1 0 ⊓ vertexCoordinateOpen R (Fin 2) 1 1))) :
    vertexTwistTwoRectangleH2LinearEquiv R a (Submodule.Quotient.mk x) =
      SheafTools.mayerVietorisGlobalConnecting (vertexTwistAbelianSheaf R (Fin 2) a)
        (vertexCoordinateOpen R (Fin 2) 0 0) (vertexCoordinateOpen R (Fin 2) 0 1)
        (vertexCoordinateOpen_cover R (Fin 2) 0) 1
        (SheafTools.rectangleRowConnecting (vertexTwistAbelianSheaf R (Fin 2) a)
          (vertexCoordinateOpen R (Fin 2) 1 0) (vertexCoordinateOpen R (Fin 2) 1 1)
          (vertexCoordinateOpen_cover R (Fin 2) 1)
          (vertexCoordinateOpen R (Fin 2) 0 0 ⊓ vertexCoordinateOpen R (Fin 2) 0 1) x) := by
  change SchemeTools.schemeBaseCoverCohomologyLinearEquiv (vertexToBase R (Fin 2))
    (vertexTwistSheaf R (Fin 2) a) _ (vertexCoordinateOpen_cover R (Fin 2) 0) 2
      (SchemeTools.schemeRectangleTopConnectingLinear (vertexToBase R (Fin 2))
        (vertexTwistSheaf R (Fin 2) a) _ _ (vertexCoordinateOpen_cover R (Fin 2) 1) _ _ x) = _
  rw [SchemeTools.schemeBaseCoverCohomologyLinearEquiv_apply]
  rfl

end BPFixedPoints.ProjectiveLine
