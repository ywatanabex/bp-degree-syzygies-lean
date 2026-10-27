import BPFixedPoints.Incidence.KoszulFaces
import BPFixedPoints.Incidence.KoszulFaceRing
import BPFixedPoints.Incidence.Torus

/-! # Identify degree-zero face quotients with existing incidence chart rings -/

namespace BPFixedPoints.CechProduct

variable {V : Type*}

@[simp] theorem decide_chartFace_one (σ : V → Bool) (v : V) :
    decide (chartFace σ v = 1) = σ v := by
  cases h : σ v <;> simp [chartFace, h]

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Multigraph

open MvPolynomial CechProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Move chart-face coefficient polynomials to the existing vertex/coefficient polynomial ring. -/
noncomputable def chartFaceAmbientEquiv (G : Multigraph V E) (σ : V → Bool) :
    MvPolynomial (IncCoeffIdx E) (FaceRing ℂ (chartFace σ)) ≃ₐ[ℂ]
      MvPolynomial (IncChartVar V E) ℂ :=
  (MvPolynomial.mapAlgEquiv (IncCoeffIdx E) (chartFaceRingEquiv (R := ℂ) σ)).trans
    ((MvPolynomial.sumAlgEquiv ℂ (IncCoeffIdx E) V).symm.trans
      (MvPolynomial.renameEquiv ℂ (Equiv.sumComm (IncCoeffIdx E) V)))

@[simp] theorem chartFaceAmbientEquiv_X (σ : V → Bool) (c : IncCoeffIdx E) :
    G.chartFaceAmbientEquiv σ (X c) = X (Sum.inr c) := by
  simp [chartFaceAmbientEquiv, MvPolynomial.mapAlgEquiv_apply,
    MvPolynomial.sumAlgEquiv_symm_X]

@[simp] theorem chartFaceAmbientEquiv_C_variable (σ : V → Bool) (v : V) :
    G.chartFaceAmbientEquiv σ (C (faceVariable ℂ (chartFace σ) v)) = X (Sum.inl v) := by
  simp [chartFaceAmbientEquiv, MvPolynomial.mapAlgEquiv_apply,
    MvPolynomial.sumAlgEquiv_symm_C_X]

theorem chartFaceAmbientEquiv_equation (σ : V → Bool) (e : E) :
    G.chartFaceAmbientEquiv σ (G.incFaceEquation (chartFace σ) e) = G.incChartEq σ e := by
  simp only [incFaceEquation, incChartEq, map_sum, map_mul, map_incCoord,
    chartFaceAmbientEquiv_X, chartFaceAmbientEquiv_C_variable, decide_chartFace_one]

theorem chartFaceIdeal_map (σ : V → Bool) :
    Ideal.span (Set.range (G.incChartEq σ)) =
      (G.incFaceIdeal (chartFace σ)).map (G.chartFaceAmbientEquiv σ).toRingHom := by
  rw [incFaceIdeal, Ideal.map_span, ← Set.range_comp]
  congr 1
  congr 1
  funext e
  exact (G.chartFaceAmbientEquiv_equation σ e).symm

/-- The actual Koszul quotient on a degree-zero face is the existing incidence chart ring. -/
noncomputable def incFaceChartEquiv (σ : V → Bool) :
    G.IncFaceRing (chartFace σ) ≃ₐ[ℂ] G.IncChartRing σ :=
  Ideal.quotientEquivAlg _ _ (G.chartFaceAmbientEquiv σ) (G.chartFaceIdeal_map σ)

@[simp] theorem incFaceChartEquiv_mk (σ : V → Bool)
    (p : MvPolynomial (IncCoeffIdx E) (FaceRing ℂ (chartFace σ))) :
    G.incFaceChartEquiv σ (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (G.chartFaceAmbientEquiv σ p) := rfl

/-- Map from a degree-zero face to the common torus. -/
noncomputable def incFaceChartMap (σ : V → Bool) :
    G.IncFaceRing (chartFace σ) →ₐ[ℂ] G.IncTorusRing :=
  (G.incChartMap σ).comp (G.incFaceChartEquiv σ).toAlgHom

theorem incFaceChartMap_injective (σ : V → Bool) :
    Function.Injective (G.incFaceChartMap σ) :=
  (G.incChartMap_injective σ).comp (G.incFaceChartEquiv σ).injective

end BPFixedPoints.Multigraph
