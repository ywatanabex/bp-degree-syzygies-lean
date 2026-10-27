import BPFixedPoints.Incidence.VertexProjectiveFaceOpens
import BPFixedPoints.Incidence.AffineOpenSectionCoordinates
import BPFixedPoints.Incidence.VertexProjectiveTwistPolynomialSections
import BPFixedPoints.Incidence.SchemeModuleCohomologyLinearity

/-! # Actual sections and original restrictions on every mixed face

The target opens are the original binary-cover intersections. Their native
structure-sheaf restrictions are the existing face-ring refinement maps.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CechProduct TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- Original face refinement is inclusion between the original rectangular opens. -/
theorem vertexBinaryFaceOpen_refinement {q r : V → Fin 3} (h : FaceRefines q r) :
    SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) r ≤
      SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q := by
  rw [← vertexFaceι_opensRange R V q, ← vertexFaceι_opensRange R V r]
  rintro x ⟨y, rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom (faceRefinementMap R h).toRingHom) y, ?_⟩
  rw [← Scheme.Hom.comp_apply, vertexFaceι_refinement]

/-- Native affine section coordinates on the independently specified original face open. -/
noncomputable def vertexFaceSectionsIso (q : V → Fin 3) :
    Γ(vertexScheme R V, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q) ≅
      CommRingCat.of (FaceRing R q) :=
  SheafTools.affineOpenSectionsIsoAt _ (vertexFaceι R V q) _ (vertexFaceι_opensRange R V q)

/-- Actual functions on every original mixed face are the original face ring. -/
noncomputable def vertexFaceSectionsEquiv (q : V → Fin 3) :
    Γ(vertexScheme R V, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q) ≃+* FaceRing R q :=
  (vertexFaceSectionsIso R V q).commRingCatIsoToRingEquiv

/-- Every actual face restriction is exactly the existing original face refinement map. -/
theorem vertexFaceSections_restrict {q r : V → Fin 3} (h : FaceRefines q r)
    (s : Γ(vertexScheme R V, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)) :
    vertexFaceSectionsEquiv R V r
      ((vertexScheme R V).presheaf.map (homOfLE (vertexBinaryFaceOpen_refinement R V h)).op s) =
        faceRefinementMap R h (vertexFaceSectionsEquiv R V q s) := by
  have hn := SheafTools.affineOpenSectionsIsoAt_naturality
    (CommRingCat.ofHom (faceRefinementMap R h).toRingHom) (vertexFaceι R V q) (vertexFaceι R V r)
    (vertexFaceι_refinement R V h) _ _ (vertexFaceι_opensRange R V q) (vertexFaceι_opensRange R V r)
    (vertexBinaryFaceOpen_refinement R V h)
  exact congrArg (fun f => f.hom s) hn

/-- The original right-to-Laurent inverse variable occurs in the actual structure-sheaf restriction. -/
theorem vertexFaceSections_refinement_variable {q r : V → Fin 3} (h : FaceRefines q r) (v : V) :
    vertexFaceSectionsEquiv R V r
      ((vertexScheme R V).presheaf.map (homOfLE (vertexBinaryFaceOpen_refinement R V h)).op
        ((vertexFaceSectionsEquiv R V q).symm (faceVariable R q v))) =
      if hf : q v = 1 ∧ r v = 2 then (↑((faceLaurentUnit R r v hf.2)⁻¹) : FaceRing R r)
      else faceVariable R r v := by
  rw [vertexFaceSections_restrict R V h, RingEquiv.apply_symm_apply, faceRefinement_variable R h]

/-- Original face coordinates retain the independently defined geometric base coefficients. -/
theorem vertexFaceSectionsEquiv_coefficient (q : V → Fin 3) (r : R) :
    vertexFaceSectionsEquiv R V q
      (SchemeTools.schemeBaseCoefficientAt (vertexToBase R V)
        (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q) r) =
      algebraMap R (FaceRing R q) r :=
  SheafTools.affineOpenSectionsIsoAt_coefficient (vertexFaceι R V q) _
    (vertexFaceι_opensRange R V q) (vertexToBase R V) _ (vertexFaceι_toBase R V q) r

/-- The actual face-section comparison is an algebra equivalence for the original geometric action. -/
noncomputable def vertexFaceSectionsAlgEquiv (q : V → Fin 3) :
    letI : Algebra R Γ(vertexScheme R V, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q) :=
      (SchemeTools.schemeBaseCoefficientAt (vertexToBase R V)
        (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)).toAlgebra
    Γ(vertexScheme R V, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q) ≃ₐ[R] FaceRing R q := by
  letI : Algebra R Γ(vertexScheme R V, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q) :=
    (SchemeTools.schemeBaseCoefficientAt (vertexToBase R V)
      (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)).toAlgebra
  exact { vertexFaceSectionsEquiv R V q with commutes' := vertexFaceSectionsEquiv_coefficient R V q }

/-- Actual twist sections on every original face have coordinates in its original mixed face ring. -/
noncomputable def vertexTwistSheafFaceSectionsWithChartEquiv (a : V → ℤ) (σ : V → Bool)
    (q : V → Fin 3) (h : FaceRefines (chartFace σ) q) :
    letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V) (vertexTwistSheaf R V a)
      (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)
    Γ(vertexTwistSheaf R V a, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q) ≃ₗ[R] FaceRing R q := by
  let U := SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q
  letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V) (vertexTwistSheaf R V a) U
  letI : Module R Γ(vertexScheme R V, U) :=
    Module.compHom _ (SchemeTools.schemeBaseCoefficientAt (vertexToBase R V) U)
  let e : Γ(vertexScheme R V, U) ≃ₗ[R] FaceRing R q :=
    { (vertexFaceSectionsEquiv R V q).toAddEquiv with
      map_smul' := by
        intro r x
        change vertexFaceSectionsEquiv R V q
          (SchemeTools.schemeBaseCoefficientAt (vertexToBase R V) U r * x) = _
        rw [map_mul, vertexFaceSectionsEquiv_coefficient, Algebra.smul_def]
        rfl }
  exact (SchemeTools.schemeBaseLocalFrameSectionLinearEquiv (vertexToBase R V)
    (vertexChartOpen R V (vertexBooleanPivot V σ)) (vertexTwistSheaf R V a)
    (vertexTwistSheafChartIso R V a (vertexBooleanPivot V σ)) U
    (vertexBinaryFaceOpen_le_chart R V σ q h)).trans e

/-- Face coordinates evaluate the specified containing chart frame and original affine coordinates. -/
theorem vertexTwistSheafFaceSectionsWithChartEquiv_apply (a : V → ℤ) (σ : V → Bool)
    (q : V → Fin 3) (h : FaceRefines (chartFace σ) q)
    (s : Γ(vertexTwistSheaf R V a, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)) :
    vertexTwistSheafFaceSectionsWithChartEquiv R V a σ q h s =
      vertexFaceSectionsEquiv R V q
        (vertexTwistSheafChartCoefficient R V a (vertexBooleanPivot V σ) _
          (vertexBinaryFaceOpen_le_chart R V σ q h) s) := rfl

/-- Within any original containing chart, all actual twist restrictions have the original face-ring formula. -/
theorem vertexTwistSheafFaceSectionsWithChartEquiv_restrict (a : V → ℤ) (σ : V → Bool)
    {q r : V → Fin 3} (hq : FaceRefines (chartFace σ) q) (h : FaceRefines q r)
    (s : Γ(vertexTwistSheaf R V a, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)) :
    vertexTwistSheafFaceSectionsWithChartEquiv R V a σ r (faceRefines_trans hq h)
      ((vertexTwistSheaf R V a).presheaf.map (homOfLE (vertexBinaryFaceOpen_refinement R V h)).op s) =
        faceRefinementMap R h (vertexTwistSheafFaceSectionsWithChartEquiv R V a σ q hq s) := by
  rw [vertexTwistSheafFaceSectionsWithChartEquiv_apply, vertexTwistSheafFaceSectionsWithChartEquiv_apply]
  have hx := vertexTwistSheafChartCoefficient_restrict R V a (vertexBooleanPivot V σ)
    (W := SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) r)
    (U := SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)
    (vertexBinaryFaceOpen_refinement R V h) (vertexBinaryFaceOpen_le_chart R V σ q hq) s
  exact (congrArg (vertexFaceSectionsEquiv R V r) hx).trans
    (vertexFaceSections_restrict R V h _)

/-- Original mixed-face section coordinates using the original left pivot on each Laurent direction. -/
noncomputable def vertexTwistSheafFaceSectionsEquiv (a : V → ℤ) (q : V → Fin 3) :
    letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V) (vertexTwistSheaf R V a)
      (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)
    Γ(vertexTwistSheaf R V a, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q) ≃ₗ[R] FaceRing R q :=
  vertexTwistSheafFaceSectionsWithChartEquiv R V a (vertexFaceBaseChoice V q) q (vertexFaceBaseChoice_refines V q)

/-- The chosen face map is exactly the original chart coefficient followed by the original mixed coordinates. -/
theorem vertexTwistSheafFaceSectionsEquiv_apply (a : V → ℤ) (q : V → Fin 3)
    (s : Γ(vertexTwistSheaf R V a, SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)) :
    vertexTwistSheafFaceSectionsEquiv R V a q s =
      vertexFaceSectionsEquiv R V q
        (vertexTwistSheafChartCoefficient R V a (vertexBooleanPivot V (vertexFaceBaseChoice V q)) _
          (vertexBinaryFaceOpen_le_chart R V _ q (vertexFaceBaseChoice_refines V q)) s) := rfl

noncomputable local instance vertexFaceSectionsHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _

/-- Actual degree-zero local Ext has the original mixed face coordinates and geometric base action. -/
noncomputable def vertexTwistSheafFaceH0LinearEquiv (a : V → ℤ) (q : V → Fin 3) :
    letI : Module R ((vertexTwistAbelianSheaf R V a).H' 0
      (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)) :=
      SchemeTools.schemeBaseLocalCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a)
        (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q) 0
    (vertexTwistAbelianSheaf R V a).H' 0 (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q) ≃ₗ[R]
      FaceRing R q := by
  letI : Module R ((vertexTwistAbelianSheaf R V a).H' 0
    (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)) :=
    SchemeTools.schemeBaseLocalCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a)
      (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q) 0
  letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V) (vertexTwistSheaf R V a)
    (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)
  exact (SchemeTools.schemeBaseLocalH0LinearEquiv (vertexToBase R V) (vertexTwistSheaf R V a)
    (SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q)).trans
      (vertexTwistSheafFaceSectionsEquiv R V a q)

end BPFixedPoints.ProjectiveLine
