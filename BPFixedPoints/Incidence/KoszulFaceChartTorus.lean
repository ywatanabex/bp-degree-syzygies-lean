import BPFixedPoints.Incidence.KoszulFaceChart
import BPFixedPoints.Incidence.KoszulFaceTorus

/-! # Degree-zero face torus maps agree with the existing chart restriction maps -/

namespace BPFixedPoints.CechProduct

@[simp] theorem faceOrientation_chartFace {V : Type*} (σ : V → Bool) :
    faceOrientation (chartFace σ) = σ := by
  funext v
  exact decide_chartFace_one σ v

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Multigraph

open MvPolynomial CechProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

@[simp] theorem incFaceChartMap_mk (σ : V → Bool)
    (p : MvPolynomial (IncCoeffIdx E) (FaceRing ℂ (chartFace σ))) :
    G.incFaceChartMap σ (Ideal.Quotient.mk _ p) =
      G.incChartMap σ (Ideal.Quotient.mk _ (G.chartFaceAmbientEquiv σ p)) := rfl

theorem incFaceToTorus_chartFace (σ : V → Bool) :
    G.incFaceToTorus (chartFace σ) = G.incFaceChartMap σ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext'
  · apply (AlgHom.cancel_right (f := (chartFaceRingEquiv (R := ℂ) σ).symm.toAlgHom)
      (chartFaceRingEquiv (R := ℂ) σ).symm.surjective).mp
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_apply, chartFaceRingEquiv_symm_X,
      IsScalarTower.toAlgHom_apply, MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mkₐ_eq_mk, incFaceChartMap_mk]
    rw [G.incFaceToTorus_C_variable, G.chartFaceAmbientEquiv_C_variable,
      G.incChartMap_mk, aeval_X, faceOrientation_chartFace]
  · intro c
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, incFaceChartMap_mk]
    rw [G.incFaceToTorus_X, G.chartFaceAmbientEquiv_X, G.incChartMap_mk, aeval_X]
    rfl

theorem incFaceToTorus_chartFace_apply (σ : V → Bool) (x : G.IncFaceRing (chartFace σ)) :
    G.incFaceToTorus (chartFace σ) x = G.incChartMap σ (G.incFaceChartEquiv σ x) :=
  AlgHom.congr_fun (G.incFaceToTorus_chartFace σ) x

theorem incFaceToTorus_chartFace_range (σ : V → Bool) :
    (G.incFaceToTorus (chartFace σ)).range = (G.incChartMap σ).range := by
  ext z
  simp only [AlgHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨G.incFaceChartEquiv σ x, (G.incFaceToTorus_chartFace_apply σ x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨(G.incFaceChartEquiv σ).symm x, ?_⟩
    rw [G.incFaceToTorus_chartFace_apply, AlgEquiv.apply_symm_apply]

end BPFixedPoints.Multigraph
