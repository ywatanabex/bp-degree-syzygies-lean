import BPFixedPoints.Incidence.IncidenceProjectiveChartFactorization

/-! # The original incidence scheme is closed in the actual projective product

The original quotient chart squares are actual pullbacks. Closed immersion
then follows from Mathlib's locality theorem on the original polynomial cover.
-/

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CechProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The original Boolean face has exactly the original incidence chart open as its image. -/
theorem incidenceFaceι_chart_opensRange (σ : V → Bool) :
    (G.incidenceFaceι (chartFace σ)).opensRange = G.incidenceChartOpen σ := by
  change _ = (G.incidenceChartι σ).opensRange
  dsimp only [incidenceChartι]
  rw [Scheme.Hom.opensRange_comp_of_isIso]

/-- The original quotient charts are genuine base changes of the actual projective morphism. -/
theorem incidenceProjectiveChart_isPullback (σ : V → Bool) :
    IsPullback (G.incidenceChartPolynomialMorphism σ) (G.incidenceFaceι (chartFace σ))
      (ProjectiveLine.vertexChartι (IncCoeffRing E) V (incidenceProjectivePivot σ))
      G.incidenceProjectiveMorphism := by
  apply IsOpenImmersion.isPullback _ _ _ _ (G.incidenceProjectiveMorphism_chart σ).symm
  change G.incidenceProjectiveMorphism ⁻¹ᵁ G.incidenceProjectiveChartOpen σ = _
  rw [G.incidenceProjectiveMorphism_preimage_chart, G.incidenceFaceι_chart_opensRange]

/-- The actual global incidence morphism is a closed immersion into the original projective product. -/
instance incidenceProjectiveMorphism_isClosedImmersion :
    IsClosedImmersion G.incidenceProjectiveMorphism := by
  apply IsZariskiLocalAtTarget.of_openCover
    (ProjectiveLine.vertexPolynomialCover (IncCoeffRing E) V).openCover
  intro τ
  let σ : V → Bool := fun v => decide (τ v = 1)
  have hp : incidenceProjectivePivot σ = τ := by
    funext v
    have hi : τ v = 0 ∨ τ v = 1 := by omega
    rcases hi with hv | hv <;> simp [incidenceProjectivePivot, σ, hv]
  have h := (G.incidenceProjectiveChart_isPullback σ).flip
  rw [hp] at h
  change IsClosedImmersion (pullback.snd G.incidenceProjectiveMorphism
    (ProjectiveLine.vertexChartι (IncCoeffRing E) V τ))
  rw [← h.isoPullback_inv_snd]
  infer_instance

end BPFixedPoints.Multigraph
