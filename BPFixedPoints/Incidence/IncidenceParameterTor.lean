import BPFixedPoints.Incidence.IncidenceParameterResolution
import BPFixedPoints.Incidence.ResolutionTorGrading

/-! # Comparing actual Tor after parameter base change at a compatible origin -/

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (a : G.IncidenceLinearParameters)

noncomputable local instance coefficientTorAlgebra :
    Algebra (IncCoeffRing E) G.IncidenceRing := G.coeffHom.toRingHom.toAlgebra

variable (B : Type) [CommRing B] [Algebra (MvPolynomial (Fin G.dG) ℂ) B]

/-- Tor over the changed coefficient ring, defined independently by the left derived functor. -/
noncomputable def incidenceParameterTor (p : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B →+* ℂ) → ModuleCat ℂ := by
  letI := G.incidenceCoefficientParameterAlgebra a
  intro e'
  exact ((ModuleCat.extendScalars e').leftDerived p).obj
    (ModuleCat.of (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B)
      ((IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B) ⊗[IncCoeffRing E] G.IncidenceRing))

variable (ha : a ∈ G.incidenceFiniteParameterLocus)

/-- Compatibility with the original coefficient origin preserves minimality. -/
theorem incidenceParameterBaseChangeResolution_minimal :
    letI := G.incidenceCoefficientParameterAlgebra a
    ∀ (e' : IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B →+* ℂ),
      ∀ (he : e'.comp (algebraMap (IncCoeffRing E)
        (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B)) = constantCoeff),
      ∀ i j, LinearMap.range ((G.incidenceParameterBaseChangeResolution a ha B).complex.d i j).hom ≤
        RingHom.ker e' • (⊤ : Submodule (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B) ((G.incidenceParameterBaseChangeResolution a ha B).complex.X j)) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  intro e' he i j
  by_cases h : j + 1 = i
  · subst i
    rw [G.incidenceParameterBaseChangeResolution_d]
    exact baseChange_minimal constantCoeff e' he (G.incFreeTermDifferential j)
      (by simpa only [G.incFreeResolution_d] using G.incFreeResolution_minimal (j + 1) j)
  · rw [(G.incidenceParameterBaseChangeResolution a ha B).complex.shape i j h]
    rw [ModuleCat.hom_zero, LinearMap.range_zero]
    exact bot_le

/-- The actual derived specialization is the specialization of the unchanged free term. -/
noncomputable def incidenceParameterTorIsoFreeTerm (p : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    ∀ (e' : IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B →+* ℂ),
      ∀ (he : e'.comp (algebraMap (IncCoeffRing E)
        (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B)) = constantCoeff),
      G.incidenceParameterTor a B p e' ≅ (ModuleCat.extendScalars e').obj
        (ModuleCat.of (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B)
          ((IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B) ⊗[IncCoeffRing E] G.IncFreeTerm p)) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  intro e' he
  exact derivedSpecializationIsoTerm e' (G.incidenceParameterBaseChangeResolution a ha B)
    (G.incidenceParameterBaseChangeResolution_minimal a B ha e' he) p

/-- The state basis is unchanged after the base change and the residue specialization. -/
noncomputable def incidenceParameterTorEquivState (p : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    ∀ (e' : IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B →+* ℂ),
      ∀ (he : e'.comp (algebraMap (IncCoeffRing E)
        (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B)) = constantCoeff),
      G.incidenceParameterTor a B p e' ≃ₗ[ℂ]
        ({b : G.IncResolutionBasis // G.incResolutionDegree b = p} →₀ ℂ) := by
  letI := G.incidenceCoefficientParameterAlgebra a
  intro e' he
  letI := e'.toAlgebra
  exact (G.incidenceParameterTorIsoFreeTerm a B ha p e' he).toLinearEquiv.trans
    (((G.incidenceParameterBaseChangeBasis a B p).baseChange ℂ).repr)

/-- Actual Tor over the changed ring agrees with actual Tor over the original ring. -/
noncomputable def incidenceParameterTorEquiv (p : ℕ) :
    letI := G.incidenceCoefficientParameterAlgebra a
    ∀ (e' : IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B →+* ℂ),
      ∀ (he : e'.comp (algebraMap (IncCoeffRing E)
        (IncCoeffRing E ⊗[MvPolynomial (Fin G.dG) ℂ] B)) = constantCoeff),
      G.incidenceParameterTor a B p e' ≃ₗ[ℂ] G.incidenceTor p := by
  letI := G.incidenceCoefficientParameterAlgebra a
  intro e' he
  exact (G.incidenceParameterTorEquivState a B ha p e' he).trans (G.incidenceTorEquivState p).symm

end BPFixedPoints.Multigraph
