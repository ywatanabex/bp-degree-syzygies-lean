import BPFixedPoints.Incidence.IncidenceProjectiveChartPreimages
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Original quotient morphisms in the actual projective-product charts

The independent original vertex polynomial chart maps surjectively to each
original incidence chart. Both its coefficient and vertex maps retain their
original formulas. The actual projective morphism factors through this map.
-/

namespace BPFixedPoints.Multigraph
open MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits CechProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Interchange the original vertex and coefficient polynomial presentations. -/
noncomputable def incidenceChartAmbientPolynomialEquiv (σ : V → Bool) :
    MvPolynomial V (IncCoeffRing E) ≃ₐ[ℂ]
      MvPolynomial (IncCoeffIdx E) (FaceRing ℂ (chartFace σ)) :=
  (sumAlgEquiv ℂ V (IncCoeffIdx E)).symm.trans (G.chartFaceAmbientEquiv σ).symm

@[simp] theorem incidenceChartAmbientPolynomialEquiv_X (σ : V → Bool) (v : V) :
    G.incidenceChartAmbientPolynomialEquiv σ (X v) = C (faceVariable ℂ (chartFace σ) v) := by
  apply (G.chartFaceAmbientEquiv σ).injective
  simp [incidenceChartAmbientPolynomialEquiv]

@[simp] theorem incidenceChartAmbientPolynomialEquiv_C_X (σ : V → Bool) (c : IncCoeffIdx E) :
    G.incidenceChartAmbientPolynomialEquiv σ (C (X c)) = X c := by
  apply (G.chartFaceAmbientEquiv σ).injective
  simp [incidenceChartAmbientPolynomialEquiv]

/-- The original polynomial chart maps to the actual incidence face quotient. -/
noncomputable def incidenceChartPolynomialHom (σ : V → Bool) :
    MvPolynomial V (IncCoeffRing E) →ₐ[ℂ] G.IncFaceRing (chartFace σ) :=
  (Ideal.Quotient.mkₐ ℂ (G.incFaceIdeal (chartFace σ))).comp
    (G.incidenceChartAmbientPolynomialEquiv σ).toAlgHom

@[simp] theorem incidenceChartPolynomialHom_X (σ : V → Bool) (v : V) :
    G.incidenceChartPolynomialHom σ (X v) = G.incidenceFaceVertexCoordinate (chartFace σ) v := by
  simp [incidenceChartPolynomialHom, incidenceFaceVertexCoordinate]

/-- Every original coefficient is preserved by the chart quotient map. -/
theorem incidenceChartPolynomialHom_C (σ : V → Bool) (p : IncCoeffRing E) :
    G.incidenceChartPolynomialHom σ (C p) = G.incidenceFaceCoefficientHom (chartFace σ) p := by
  have he : (G.incidenceChartPolynomialHom σ).comp
      (IsScalarTower.toAlgHom ℂ (IncCoeffRing E) (MvPolynomial V (IncCoeffRing E))) =
        G.incidenceFaceCoefficientHom (chartFace σ) := by
    apply MvPolynomial.algHom_ext
    intro c
    change G.incidenceChartPolynomialHom σ (C (X c)) = _
    simp [incidenceChartPolynomialHom]
  exact congrArg (fun h => h p) he

/-- The actual original chart map is a quotient, on the full rings rather than only points. -/
theorem incidenceChartPolynomialHom_surjective (σ : V → Bool) :
    Function.Surjective (G.incidenceChartPolynomialHom σ) :=
  Ideal.Quotient.mk_surjective.comp (G.incidenceChartAmbientPolynomialEquiv σ).surjective

/-- The genuine closed quotient morphism in the original vertex polynomial chart. -/
noncomputable def incidenceChartPolynomialMorphism (σ : V → Bool) :
    G.incidenceAffineFace (chartFace σ) ⟶
      Spec (CommRingCat.of (MvPolynomial V (IncCoeffRing E))) :=
  Spec.map (CommRingCat.ofHom (G.incidenceChartPolynomialHom σ).toRingHom)

instance incidenceChartPolynomialMorphism_isClosedImmersion (σ : V → Bool) :
    IsClosedImmersion (G.incidenceChartPolynomialMorphism σ) :=
  IsClosedImmersion.spec_of_surjective _ (G.incidenceChartPolynomialHom_surjective σ)

/-- Every original face is an object over its original coefficient scheme. -/
noncomputable def incidenceFaceOverBase (q : V → Fin 3) :
    Over (Spec (CommRingCat.of (IncCoeffRing E))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (R := IncCoeffRing E) (S := G.IncFaceRing q)
    (G.incidenceFaceCoefficientHom q).toRingHom))

/-- The actual polynomial chart quotient is a morphism over the original coefficient scheme. -/
noncomputable def incidenceChartPolynomialOver (σ : V → Bool) :
    G.incidenceFaceOverBase (chartFace σ) ⟶ SchemeTools.polynomialOverBase (IncCoeffRing E) V :=
  Over.homMk (G.incidenceChartPolynomialMorphism σ) (by
    change Spec.map (CommRingCat.ofHom (G.incidenceChartPolynomialHom σ).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (IncCoeffRing E)
        (MvPolynomial V (IncCoeffRing E)))) =
      Spec.map (CommRingCat.ofHom (R := IncCoeffRing E) (S := G.IncFaceRing (chartFace σ))
        (G.incidenceFaceCoefficientHom (chartFace σ)).toRingHom)
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    exact G.incidenceChartPolynomialHom_C σ p)

/-- The face inclusion followed by the global projective map, over the same original base. -/
noncomputable def incidenceFaceProjectiveOver (q : V → Fin 3) :
    G.incidenceFaceOverBase q ⟶ ProjectiveLine.vertexOverBase (IncCoeffRing E) V :=
  Over.homMk (G.incidenceFaceι q ≫ G.incidenceProjectiveMorphism) (by
    change (G.incidenceFaceι q ≫ G.incidenceProjectiveMorphism) ≫
      ProjectiveLine.vertexToBase (IncCoeffRing E) V =
        Spec.map (CommRingCat.ofHom (R := IncCoeffRing E) (S := G.IncFaceRing q)
          (G.incidenceFaceCoefficientHom q).toRingHom)
    rw [Category.assoc, G.incidenceProjectiveMorphism_toBase, G.incidenceFaceι_coefficient])

/-- The chart quotient followed by an original vertex evaluation retains that same coordinate. -/
@[reassoc] theorem incidenceChartPolynomialMorphism_vertex (σ : V → Bool) (v : V) :
    G.incidenceChartPolynomialMorphism σ ≫
        Spec.map (CommRingCat.ofHom
          (Polynomial.aeval (X v : MvPolynomial V (IncCoeffRing E))).toRingHom) ≫
          ProjectiveLine.chartι (IncCoeffRing E) (incidenceProjectivePivot σ v) =
      G.incidenceFaceVertexMorphism (chartFace σ) v := by
  have hp : incidenceFaceVertexPivot (chartFace σ v) = incidenceProjectivePivot σ v := by
    cases hb : σ v <;> simp [incidenceFaceVertexPivot, incidenceProjectivePivot, chartFace, hb]
  dsimp only [incidenceChartPolynomialMorphism, incidenceFaceVertexMorphism,
    ProjectiveLine.evaluationChart]
  rw [hp, ← Spec.map_comp_assoc]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  change (G.incidenceChartPolynomialHom σ).toRingHom.comp
    (Polynomial.aeval (X v : MvPolynomial V (IncCoeffRing E))).toRingHom =
      Polynomial.eval₂RingHom (G.incidenceFaceCoefficientHom (chartFace σ)).toRingHom
        (G.incidenceFaceVertexCoordinate (chartFace σ) v)
  apply Polynomial.ringHom_ext
  · intro p
    simpa using G.incidenceChartPolynomialHom_C σ p
  · simp

/-- The actual global projective map is the original quotient on every original chart. -/
@[reassoc] theorem incidenceProjectiveMorphism_chart (σ : V → Bool) :
    G.incidenceChartPolynomialMorphism σ ≫
        ProjectiveLine.vertexChartι (IncCoeffRing E) V (incidenceProjectivePivot σ) =
      G.incidenceFaceι (chartFace σ) ≫ G.incidenceProjectiveMorphism := by
  have he : G.incidenceChartPolynomialOver σ ≫
      ProjectiveLine.vertexChartOver (IncCoeffRing E) V (incidenceProjectivePivot σ) =
        G.incidenceFaceProjectiveOver (chartFace σ) := by
    apply (ProjectiveLine.vertexIsProduct (IncCoeffRing E) V).hom_ext
    intro ⟨v⟩
    apply Over.OverMorphism.ext
    change (G.incidenceChartPolynomialMorphism σ ≫
      ProjectiveLine.vertexChartι (IncCoeffRing E) V (incidenceProjectivePivot σ)) ≫
        (ProjectiveLine.vertexProjectionOver (IncCoeffRing E) V v).left =
      (G.incidenceFaceι (chartFace σ) ≫ G.incidenceProjectiveMorphism) ≫
        (ProjectiveLine.vertexProjectionOver (IncCoeffRing E) V v).left
    rw [Category.assoc, ProjectiveLine.vertexChartι_projection,
      G.incidenceChartPolynomialMorphism_vertex, Category.assoc,
      G.incidenceFaceι_projective_projection]
  exact congrArg Over.Hom.left he

end BPFixedPoints.Multigraph
