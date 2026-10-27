import BPFixedPoints.Incidence.VertexProjectiveFaceMorphisms
import BPFixedPoints.Incidence.VertexProjectiveTwistHigherCohomology

/-! # Actual opens of the original mixed-coordinate faces

Existing face refinements are localizations at the coordinates that become
Laurent. The geometric chart inverse images use those same coordinates.
-/

namespace BPFixedPoints.CechProduct
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R] {V : Type} [Fintype V] [DecidableEq V]

/-- In original chart coordinates the denominator inverts exactly the Laurent directions. -/
theorem chartFaceRingEquiv_refinementDen (σ : V → Bool) (q : V → Fin 3)
    (h : FaceRefines (chartFace σ) q) :
    chartFaceRingEquiv (R := R) σ (refinementDen R (chartFace σ) q) =
      ∏ v, if q v = 2 then (MvPolynomial.X v : MvPolynomial V R) else 1 := by
  rw [refinementDen_eq_prod, map_prod]
  apply Finset.prod_congr rfl
  intro v _
  by_cases hv : q v = 2
  · simp [hv]
  · have he := (h v).resolve_right hv
    simp [hv, he]

end BPFixedPoints.CechProduct

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CechProduct TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- A vertex coordinate open pulls back to its original polynomial basic open. -/
theorem vertexChartι_preimage_coordinateOpen (σ : V → Fin 2) (v : V) (i : Fin 2) :
    vertexChartι R V σ ⁻¹ᵁ vertexCoordinateOpen R V v i =
      PrimeSpectrum.basicOpen (if i = σ v then (1 : MvPolynomial V R) else MvPolynomial.X v) := by
  change (vertexChartι R V σ ≫ (vertexProjectionOver R V v).left) ⁻¹ᵁ standardOpen R i = _
  rw [vertexChartι_projection]
  exact evaluationChart_preimage_standardOpen (algebraMap R (MvPolynomial V R)) (MvPolynomial.X v) (σ v) i

omit [DecidableEq V] in
/-- A containing original chart sees exactly the Laurent-coordinate principal open of a face. -/
theorem vertexChartι_preimage_binaryFace (σ : V → Bool) (q : V → Fin 3)
    (h : FaceRefines (chartFace σ) q) :
    vertexChartι R V (vertexBooleanPivot V σ) ⁻¹ᵁ
      SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q =
        PrimeSpectrum.basicOpen (∏ v, if q v = 2 then (MvPolynomial.X v : MvPolynomial V R) else 1) := by
  have hf (v : V) : vertexChartι R V (vertexBooleanPivot V σ) ⁻¹ᵁ
      SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R V v) (q v) =
        PrimeSpectrum.basicOpen (if q v = 2 then (MvPolynomial.X v : MvPolynomial V R) else 1) := by
    rcases h v with he | he
    · rw [← he]
      cases hv : σ v <;> simp [chartFace, hv, SheafTools.binaryCoverFaceFactor,
        vertexChartι_preimage_coordinateOpen, vertexBooleanPivot]
    · rw [he]
      change vertexChartι R V (vertexBooleanPivot V σ) ⁻¹ᵁ
        (vertexCoordinateOpen R V v 0 ⊓ vertexCoordinateOpen R V v 1) = _
      rw [Scheme.Hom.preimage_inf, vertexChartι_preimage_coordinateOpen, vertexChartι_preimage_coordinateOpen]
      cases hv : σ v <;> simp [vertexBooleanPivot, hv]
  ext x
  change vertexChartι R V (vertexBooleanPivot V σ) x ∈
    ((⨅ v, SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R V v) (q v) : (vertexScheme R V).Opens) : Set (vertexScheme R V)) ↔ _
  rw [Opens.coe_iInf]
  simp only [Set.mem_iInter]
  change (∀ v, x ∈ vertexChartι R V (vertexBooleanPivot V σ) ⁻¹ᵁ
    SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R V v) (q v)) ↔ _
  simp only [hf]
  change (∀ v, (if q v = 2 then (MvPolynomial.X v : MvPolynomial V R) else 1) ∉ x.asIdeal) ↔
    (∏ v, if q v = 2 then (MvPolynomial.X v : MvPolynomial V R) else 1) ∉ x.asIdeal
  simp only [Ideal.IsPrime.prod_mem_iff, not_exists, not_and, Finset.mem_univ, true_implies]

/-- Choose a containing original chart, retaining the right pivots of polynomial faces. -/
def vertexFaceBaseChoice (q : V → Fin 3) : V → Bool := fun v => decide (q v = 1)

omit [Fintype V] [DecidableEq V] in
/-- The chosen containing chart refines to exactly the original mixed face. -/
theorem vertexFaceBaseChoice_refines (q : V → Fin 3) :
    FaceRefines (chartFace (vertexFaceBaseChoice V q)) q := by
  intro v
  unfold chartFace vertexFaceBaseChoice
  generalize q v = j
  fin_cases j <;> simp

omit [DecidableEq V] in
/-- An original face is contained in every original chart refining to it. -/
theorem vertexBinaryFaceOpen_le_chart (σ : V → Bool) (q : V → Fin 3)
    (h : FaceRefines (chartFace σ) q) :
    SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q ≤
      vertexChartOpen R V (vertexBooleanPivot V σ) := by
  rw [vertexChartOpen_eq_coordinateOpen]
  apply le_iInf
  intro v
  apply (iInf_le (fun w => SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R V w) (q w)) v).trans
  rcases h v with he | he
  · rw [← he]
    cases hv : σ v <;> simp [chartFace, vertexBooleanPivot, hv, SheafTools.binaryCoverFaceFactor]
  · rw [he]
    cases hv : σ v <;> simp [vertexBooleanPivot, hv, SheafTools.binaryCoverFaceFactor]

/-- The overlap-free face map is an original open chart. -/
instance vertexFaceι_chart_isOpenImmersion (σ : V → Bool) :
    IsOpenImmersion (vertexFaceι R V (chartFace σ)) := by
  rw [← vertexFaceι_chart]
  change IsOpenImmersion (Spec.map (chartFaceRingEquiv (R := R) σ).toRingEquiv.toCommRingCatIso.inv ≫ _)
  infer_instance

/-- Refinement realizes the original face localization as an actual open immersion. -/
theorem vertexFaceRefinement_isOpenImmersion {q r : V → Fin 3} (h : FaceRefines q r) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (faceRefinementMap R h).toRingHom)) := by
  let := (faceRefinementMap R h).toRingHom.toAlgebra
  let := faceRefinement_isLocalization R h
  exact IsOpenImmersion.of_isLocalization (S := FaceRing R r) (refinementDen R q r)

/-- Every original mixed face is an actual affine open chart of the original product. -/
instance vertexFaceι_isOpenImmersion (q : V → Fin 3) : IsOpenImmersion (vertexFaceι R V q) := by
  let σ := vertexFaceBaseChoice V q
  have h := vertexFaceBaseChoice_refines V q
  have := vertexFaceRefinement_isOpenImmersion R V h
  rw [← vertexFaceι_refinement R V h]
  infer_instance

/-- The spectrum of the existing face localization has exactly its original denominator open. -/
theorem vertexFaceRefinement_opensRange {q r : V → Fin 3} (h : FaceRefines q r) :
    letI := vertexFaceRefinement_isOpenImmersion R V h
    (Spec.map (CommRingCat.ofHom (faceRefinementMap R h).toRingHom)).opensRange =
      PrimeSpectrum.basicOpen (refinementDen R q r) := by
  let := (faceRefinementMap R h).toRingHom.toAlgebra
  let := faceRefinement_isLocalization R h
  apply SetLike.ext'
  exact PrimeSpectrum.localization_away_comap_range (FaceRing R r) (refinementDen R q r)

/-- The original face chart has the original polynomial-chart image. -/
theorem vertexFaceι_chart_opensRange (σ : V → Bool) :
    (vertexFaceι R V (chartFace σ)).opensRange = vertexChartOpen R V (vertexBooleanPivot V σ) := by
  simp only [← vertexFaceι_chart]
  change (Spec.map (chartFaceRingEquiv (R := R) σ).toRingEquiv.toCommRingCatIso.inv ≫
    vertexChartι R V (vertexBooleanPivot V σ)).opensRange = _
  exact Scheme.Hom.opensRange_comp_of_isIso _ _

/-- The original face chart pulls the actual rectangular intersection back to its existing denominator. -/
theorem vertexFaceι_chart_preimage (σ : V → Bool) (q : V → Fin 3)
    (h : FaceRefines (chartFace σ) q) :
    vertexFaceι R V (chartFace σ) ⁻¹ᵁ
      SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q =
        PrimeSpectrum.basicOpen (refinementDen R (chartFace σ) q) := by
  rw [← vertexFaceι_chart]
  change Spec.map (CommRingCat.ofHom (chartFaceRingEquiv (R := R) σ).symm.toRingHom) ⁻¹ᵁ
    (vertexChartι R V (vertexBooleanPivot V σ) ⁻¹ᵁ
      SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q) = _
  rw [vertexChartι_preimage_binaryFace R V σ q h, SpecMap_preimage_basicOpen]
  congr 1
  rw [← chartFaceRingEquiv_refinementDen R σ q h]
  exact (chartFaceRingEquiv (R := R) σ).symm_apply_apply _

/-- The original mixed-coordinate spectrum is exactly the original rectangular intersection open. -/
theorem vertexFaceι_opensRange (q : V → Fin 3) :
    (vertexFaceι R V q).opensRange =
      SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen R V) q := by
  let σ := vertexFaceBaseChoice V q
  have h := vertexFaceBaseChoice_refines V q
  have := vertexFaceRefinement_isOpenImmersion R V h
  simp only [← vertexFaceι_refinement R V h]
  rw [Scheme.Hom.opensRange_comp,
    vertexFaceRefinement_opensRange, ← vertexFaceι_chart_preimage R V σ q h,
    Scheme.Hom.image_preimage_eq_opensRange_inf, vertexFaceι_chart_opensRange]
  exact inf_eq_right.mpr (vertexBinaryFaceOpen_le_chart R V σ q h)

end BPFixedPoints.ProjectiveLine
