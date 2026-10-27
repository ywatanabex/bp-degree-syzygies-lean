import BPFixedPoints.Incidence.ChartCoefficientGrading
import BPFixedPoints.Incidence.ResolutionInternalGrading
import BPFixedPoints.Incidence.ResolutionAugmentation

/-!
# Natural coefficient grading and incidence augmentation

Give vertex coordinates degree zero and free coefficients degree one on every
affine chart. This definition is independent of the free resolution. Prove
that the actual augmentation preserves this grading.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial CechProduct ResolutionTools

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Restrict an incidence section to any affine chart. -/
noncomputable def incidenceChartSection (σ : V → Bool) :
    G.IncidenceRing →ₐ[ℂ] G.IncChartRing σ :=
  (AlgEquiv.ofInjective (G.incChartMap σ) (G.incChartMap_injective σ)).symm.toAlgHom.comp
    (Subalgebra.inclusion (iInf_le _ σ))

@[simp] theorem incChartMap_incidenceChartSection (σ : V → Bool) (x : G.IncidenceRing) :
    G.incChartMap σ (G.incidenceChartSection σ x) = x.val := by
  exact congrArg Subtype.val
    ((AlgEquiv.ofInjective (G.incChartMap σ) (G.incChartMap_injective σ)).apply_symm_apply
      (Subalgebra.inclusion (iInf_le _ σ) x))

/-- A section as a polynomial in a chart's free coefficients. -/
noncomputable def incidenceChartPolynomial (σ : V → Bool) :
    G.IncidenceRing →ₗ[ℂ] MvPolynomial (E × Fin 3) (FaceRing ℂ (chartFace σ)) :=
  ((G.incFaceFreeEquiv (chartFace σ)).toLinearEquiv.restrictScalars ℂ).toLinearMap.comp
    ((G.incFaceChartEquiv σ).symm.toLinearEquiv.toLinearMap.comp
      (G.incidenceChartSection σ).toLinearMap)

theorem incidenceChartPolynomial_injective (σ : V → Bool) :
    Function.Injective (G.incidenceChartPolynomial σ) := by
  intro x y h
  apply Subtype.val_injective
  have hc := (G.incFaceChartEquiv σ).symm.injective
    ((G.incFaceFreeEquiv (chartFace σ)).injective h)
  simpa using congrArg (G.incChartMap σ) hc

@[simp] theorem incidenceChartPolynomial_one (σ : V → Bool) :
    G.incidenceChartPolynomial σ 1 = 1 := by
  change G.incFaceFreeEquiv _ ((G.incFaceChartEquiv σ).symm (G.incidenceChartSection σ 1)) = 1
  simp

theorem incidenceChartPolynomial_mul (σ : V → Bool) (x y : G.IncidenceRing) :
    G.incidenceChartPolynomial σ (x * y) =
      G.incidenceChartPolynomial σ x * G.incidenceChartPolynomial σ y := by
  change G.incFaceFreeEquiv _ ((G.incFaceChartEquiv σ).symm
    (G.incidenceChartSection σ (x * y))) = _
  simp only [map_mul]
  rfl

/-- Natural graded pieces on all affine charts, independent of the free resolution. -/
noncomputable def incidenceCoefficientPiece (n : ℕ) : Submodule ℂ G.IncidenceRing :=
  ⨅ σ, ((homogeneousSubmodule (E × Fin 3) (FaceRing ℂ (chartFace σ)) n).restrictScalars ℂ).comap (G.incidenceChartPolynomial σ)

theorem mem_incidenceCoefficientPiece (n : ℕ) (x : G.IncidenceRing) :
    x ∈ G.incidenceCoefficientPiece n ↔
      ∀ σ, (G.incidenceChartPolynomial σ x).IsHomogeneous n := by
  simp [incidenceCoefficientPiece]

theorem one_mem_incidenceCoefficientPiece : (1 : G.IncidenceRing) ∈ G.incidenceCoefficientPiece 0 := by
  rw [G.mem_incidenceCoefficientPiece]
  intro σ
  rw [G.incidenceChartPolynomial_one]
  exact isHomogeneous_one _ _

theorem mul_mem_incidenceCoefficientPiece {m n : ℕ} {x y : G.IncidenceRing}
    (hx : x ∈ G.incidenceCoefficientPiece m) (hy : y ∈ G.incidenceCoefficientPiece n) :
    x * y ∈ G.incidenceCoefficientPiece (m + n) := by
  rw [G.mem_incidenceCoefficientPiece] at hx hy ⊢
  intro σ
  rw [G.incidenceChartPolynomial_mul]
  exact (hx σ).mul (hy σ)

theorem incidenceChartPolynomial_coeffHom_X (σ : V → Bool) (c : IncCoeffIdx E) :
    G.incidenceChartPolynomial σ (G.coeffHom (X c)) =
      G.incFaceFreeEquiv (chartFace σ) (Ideal.Quotient.mk _ (X c)) := by
  apply congrArg (G.incFaceFreeEquiv (chartFace σ))
  apply (G.incFaceChartEquiv σ).injective
  apply G.incChartMap_injective σ
  change G.incChartMap σ (G.incFaceChartEquiv σ ((G.incFaceChartEquiv σ).symm
    (G.incidenceChartSection σ (G.coeffHom (X c))))) = _
  rw [AlgEquiv.apply_symm_apply, G.incChartMap_incidenceChartSection,
    ← G.incFaceToTorus_chartFace_apply, G.incFaceToTorus_X]
  simp [coeffHom]

/-- The original coefficient map S→U preserves degrees. -/
theorem coeffHom_coefficient_degree {p : IncCoeffRing E} {n : ℕ}
    (hp : p.IsHomogeneous n) : G.coeffHom p ∈ G.incidenceCoefficientPiece n := by
  rw [G.mem_incidenceCoefficientPiece]
  intro σ
  let f := AlgHom.ofLinearMap (G.incidenceChartPolynomial σ)
    (G.incidenceChartPolynomial_one σ) (G.incidenceChartPolynomial_mul σ)
  have he : f.comp G.coeffHom = aeval (fun c => f (G.coeffHom (X c))) := by
    apply MvPolynomial.algHom_ext
    intro c
    simp
  change (f.comp G.coeffHom p).IsHomogeneous n
  rw [he]
  have hv (c : IncCoeffIdx E) : (f (G.coeffHom (X c))).IsHomogeneous 1 := by
    change (G.incidenceChartPolynomial σ (G.coeffHom (X c))).IsHomogeneous 1
    rw [G.incidenceChartPolynomial_coeffHom_X]
    exact G.incFaceFreeEquiv_mk_homogeneous _ (isHomogeneous_X _ c)
  simpa only [one_mul] using hp.aeval (fun c => f (G.coeffHom (X c))) hv

/-- Restricting the augmentation to a chart gives the same local Koszul-quotient projection. -/
theorem incidenceChartPolynomial_augmentation
    (x : gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) (σ : V → Bool) :
    G.incidenceChartPolynomial σ (G.incResolutionAugmentation x) =
      G.incFaceFreeEquiv (chartFace σ)
        (G.incKoszulContraction.p (G.incResolutionInclusion x.val) (chartFace σ)) := by
  apply congrArg (G.incFaceFreeEquiv (chartFace σ))
  apply (G.incFaceChartEquiv σ).injective
  apply G.incChartMap_injective σ
  change G.incChartMap σ (G.incFaceChartEquiv σ ((G.incFaceChartEquiv σ).symm
    (G.incidenceChartSection σ (G.incResolutionAugmentation x)))) = _
  rw [AlgEquiv.apply_symm_apply, G.incChartMap_incidenceChartSection,
    G.incResolutionAugmentation_val, G.incResolutionTorusAugmentation_apply,
    ← G.incFaceToTorus_chartFace_apply]
  exact G.incQuotientCycle_torus_eq _ (G.incResolutionQuotient_mem_zero x.val x.property)
    (G.incResolutionQuotient_cycle x.val x.property) _ _

/-- The actual free-resolution augmentation preserves the original ring's natural coefficient grading. -/
theorem incResolutionAugmentation_coefficient_degree (n : ℕ)
    (x : gradedPiece (IncCoeffRing E) G.incResolutionDegree 0)
    (hx : x.val ∈ G.incResolutionInternalPiece (n : ℤ)) :
    G.incResolutionAugmentation x ∈ G.incidenceCoefficientPiece n := by
  rw [G.mem_incidenceCoefficientPiece]
  intro σ
  rw [G.incidenceChartPolynomial_augmentation, G.incKoszulContraction_p]
  apply G.incFaceFreeEquiv_mk_homogeneous
  apply polynomialFaceEquiv_homogeneous
  have hi := G.incResolutionInclusion_internal_degree (n : ℤ) hx ∅
  intro b
  have hb := hi b
  simpa [incCechInternalPiece, homogeneousCoeffPiece] using hb

end BPFixedPoints.Multigraph
