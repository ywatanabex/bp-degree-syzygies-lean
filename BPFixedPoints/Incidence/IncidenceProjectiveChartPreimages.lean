import BPFixedPoints.Incidence.IncidenceProjectiveMorphism
import BPFixedPoints.Incidence.ProjectiveProductChartImages

/-! # Original incidence charts are actual projective-chart inverse images

The local prime-ideal criterion is exactly the existing face localization
denominator. This compares every boundary point, not only the common torus.
-/

namespace BPFixedPoints.Multigraph
open MvPolynomial AlgebraicGeometry CategoryTheory CechProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The original Boolean chart choice in the actual two-coordinate projective line. -/
def incidenceProjectivePivot (σ : V → Bool) (v : V) : Fin 2 := if σ v then 1 else 0

/-- Actual target open corresponding to an original Boolean incidence chart. -/
noncomputable def incidenceProjectiveChartOpen (_G : Multigraph V E) (σ : V → Bool) :
    (ProjectiveLine.vertexScheme (IncCoeffRing E) V).Opens :=
  ProjectiveLine.vertexChartOpen (IncCoeffRing E) V (incidenceProjectivePivot σ)

/-- A vertex's actual standard-open condition is precisely its original overlap denominator. -/
theorem incidenceFaceVertexMorphism_mem_standardOpen (q : V → Fin 3) (σ : V → Bool)
    (v : V) (x : G.incidenceAffineFace q) :
    G.incidenceFaceVertexMorphism q v x ∈
        ProjectiveLine.standardOpen (IncCoeffRing E) (incidenceProjectivePivot σ v) ↔
      q v ≠ faceJoin q (chartFace σ) v → G.incidenceFaceVertexCoordinate q v ∉ x.asIdeal := by
  change x ∈ ProjectiveLine.evaluationChart (R := IncCoeffRing E) (A := G.IncFaceRing q)
    (G.incidenceFaceCoefficientHom q).toRingHom
    (G.incidenceFaceVertexCoordinate q v) (incidenceFaceVertexPivot (q v)) ⁻¹ᵁ
      ProjectiveLine.standardOpen (IncCoeffRing E) (incidenceProjectivePivot σ v) ↔ _
  rw [ProjectiveLine.evaluationChart_preimage_standardOpen]
  change (if incidenceProjectivePivot σ v = incidenceFaceVertexPivot (q v)
    then (1 : G.IncFaceRing q) else G.incidenceFaceVertexCoordinate q v) ∉ x.asIdeal ↔ _
  by_cases hq : q v = 2
  · have hu : G.incidenceFaceVertexCoordinate q v ∉ x.asIdeal :=
      by
        have hh := Ideal.notMem_of_isUnit x.asIdeal (G.incidenceFaceVertexUnit q v hq).isUnit
        simpa only [incidenceFaceVertexUnit_val] using hh
    cases hb : σ v <;>
      simp [incidenceProjectivePivot, incidenceFaceVertexPivot, faceJoin, chartFace, hq, hb, hu, x.isPrime.one_notMem]
  · have hh : q v = 0 ∨ q v = 1 := by omega
    rcases hh with hh | hh <;> cases hb : σ v <;>
      simp [incidenceProjectivePivot, incidenceFaceVertexPivot, faceJoin, chartFace, hh, hb, x.isPrime.one_notMem]

/-- On every original face the target-chart inverse image is the prescribed localization face. -/
theorem incidenceFace_projective_chart_iff (q : V → Fin 3) (σ : V → Bool)
    (x : G.incidenceAffineFace q) :
    G.incidenceProjectiveMorphism (G.incidenceFaceι q x) ∈
        G.incidenceProjectiveChartOpen σ ↔
      x ∈ Set.range (G.incidenceFaceMap (faceRefines_join_left q (chartFace σ))) := by
  rw [incidenceProjectiveChartOpen, ProjectiveLine.mem_vertexChartOpen]
  trans ∀ v, G.incidenceFaceVertexMorphism q v x ∈
    ProjectiveLine.standardOpen (IncCoeffRing E) (incidenceProjectivePivot σ v)
  · apply forall_congr'
    intro v
    change (G.incidenceFaceι q ≫ G.incidenceProjectiveMorphism ≫
      (ProjectiveLine.vertexProjectionOver (IncCoeffRing E) V v).left) x ∈ _ ↔ _
    rw [G.incidenceFaceι_projective_projection]
    rfl
  · rw [G.incidenceFaceMap_mem_range, G.incidenceRefinementDen_not_mem]
    exact forall_congr' (fun v => G.incidenceFaceVertexMorphism_mem_standardOpen q σ v x)

/-- The exact inverse image of another face image is its genuine join localization. -/
theorem incidenceFaceι_mem_face_range (q r : V → Fin 3) (x : G.incidenceAffineFace q) :
    G.incidenceFaceι q x ∈ Set.range (G.incidenceFaceι r) ↔
      x ∈ Set.range (G.incidenceFaceMap (faceRefines_join_left q r)) := by
  constructor
  · intro hx
    have hj : G.incidenceFaceι q x ∈ Set.range (G.incidenceFaceι (faceJoin q r)) := by
      rw [G.incidenceFaceι_join_range]
      exact ⟨⟨x, rfl⟩, hx⟩
    obtain ⟨z, hz⟩ := hj
    refine ⟨z, ?_⟩
    apply (G.incidenceFaceι q).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, G.incidenceFaceι_naturality]
    exact hz
  · rintro ⟨z, rfl⟩
    refine ⟨G.incidenceFaceMap (faceRefines_join_right q r) z, ?_⟩
    rw [← Scheme.Hom.comp_apply, G.incidenceFaceι_naturality,
      ← Scheme.Hom.comp_apply, G.incidenceFaceι_naturality]

/-- The original Boolean chart is precisely the actual projective-chart inverse image. -/
theorem incidenceProjectiveMorphism_preimage_chart (σ : V → Bool) :
    G.incidenceProjectiveMorphism ⁻¹ᵁ G.incidenceProjectiveChartOpen σ =
      G.incidenceChartOpen σ := by
  ext x
  obtain ⟨q, y, rfl⟩ := G.incidenceFaceι_jointly_surjective x
  have hr : Set.range (G.incidenceChartι σ) = Set.range (G.incidenceFaceι (chartFace σ)) := by
    change Set.range (G.incidenceFaceι (chartFace σ) ∘ (G.incidenceChartFaceIso σ).hom) = _
    have hs : Function.Surjective (G.incidenceChartFaceIso σ).hom := by
      intro z
      refine ⟨(G.incidenceChartFaceIso σ).inv z, ?_⟩
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    rw [Set.range_comp, Set.range_eq_univ.mpr hs, Set.image_univ]
  change G.incidenceProjectiveMorphism (G.incidenceFaceι q y) ∈
    G.incidenceProjectiveChartOpen σ ↔ G.incidenceFaceι q y ∈ Set.range (G.incidenceChartι σ)
  rw [hr, G.incidenceFace_projective_chart_iff, G.incidenceFaceι_mem_face_range]

end BPFixedPoints.Multigraph
