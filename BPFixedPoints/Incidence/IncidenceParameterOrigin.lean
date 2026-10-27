import BPFixedPoints.Incidence.IncidenceCoefficientParameters
import BPFixedPoints.Incidence.TensorProductOrigin

/-! # The coefficient origin on parameter cuts -/

namespace BPFixedPoints.Multigraph

open ResolutionTools MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (a : G.IncidenceLinearParameters)

theorem incidenceCoefficientParameter_origin :
    letI := G.incidenceCoefficientParameterAlgebra a
    (constantCoeff : IncCoeffRing E →+* ℂ).comp
      (algebraMap (MvPolynomial (Fin G.dG) ℂ) (IncCoeffRing E)) = constantCoeff := by
  letI := G.incidenceCoefficientParameterAlgebra a
  change constantCoeff.comp
    (aeval (polynomialLinearForm ∘ G.incidenceCoefficientParameterVector a)).toRingHom = _
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    classical
    simp [polynomialLinearForm, Finsupp.linearCombination_apply, Finsupp.sum]

variable (B : Type) [CommRing B] [Algebra (MvPolynomial (Fin G.dG) ℂ) B]
  (e : B →+* ℂ)
  (he : e.comp (algebraMap (MvPolynomial (Fin G.dG) ℂ) B) = constantCoeff)

/-- The actual tensor-product residue map induced by the two compatible origins. -/
noncomputable def incidenceParameterCoefficientOrigin :
    letI := G.incidenceCoefficientParameterAlgebra a
    IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B →+* ℂ := by
  letI := G.incidenceCoefficientParameterAlgebra a
  exact tensorProductOrigin constantCoeff constantCoeff e
    (G.incidenceCoefficientParameter_origin a) he

@[simp] theorem incidenceParameterCoefficientOrigin_tmul (s : IncCoeffRing E) (b : B) :
    letI := G.incidenceCoefficientParameterAlgebra a
    G.incidenceParameterCoefficientOrigin a B e he (s ⊗ₜ[MvPolynomial (Fin G.dG) ℂ] b) =
      constantCoeff s * e b := rfl

theorem incidenceParameterCoefficientOrigin_compatible :
    letI := G.incidenceCoefficientParameterAlgebra a
    (G.incidenceParameterCoefficientOrigin a B e he).comp
      (algebraMap (IncCoeffRing E) (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B)) =
      constantCoeff := by
  letI := G.incidenceCoefficientParameterAlgebra a
  apply RingHom.ext
  intro s
  simp [Algebra.TensorProduct.algebraMap_apply]

/-- Every parameter ideal contained in the origin has a canonical residue map. -/
noncomputable def incidenceParameterQuotientOrigin
    (I : Ideal (MvPolynomial (Fin G.dG) ℂ)) (hI : I ≤ RingHom.ker constantCoeff) :
    (MvPolynomial (Fin G.dG) ℂ ⧸ I) →+* ℂ :=
  Ideal.Quotient.lift I constantCoeff hI

theorem incidenceParameterQuotientOrigin_compatible
    (I : Ideal (MvPolynomial (Fin G.dG) ℂ)) (hI : I ≤ RingHom.ker constantCoeff) :
    (G.incidenceParameterQuotientOrigin I hI).comp
      (algebraMap (MvPolynomial (Fin G.dG) ℂ) (MvPolynomial (Fin G.dG) ℂ ⧸ I)) =
      constantCoeff := by
  apply RingHom.ext
  intro t
  exact Ideal.Quotient.lift_mk I constantCoeff hI

end BPFixedPoints.Multigraph
