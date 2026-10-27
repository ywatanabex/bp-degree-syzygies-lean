import BPFixedPoints.Incidence.IncidenceParameterFree
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Arbitrary base change and actual quotients of the incidence parameter algebra -/

namespace BPFixedPoints.Multigraph

open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (a : G.IncidenceLinearParameters)

/-- Finite freeness, faithful flatness and the rank survive every nonzero base change. -/
theorem incidence_parameter_baseChange (ha : a ∈ G.incidenceFiniteParameterLocus)
    (B : Type*) [CommRing B] [Nontrivial B] [Algebra (MvPolynomial (Fin G.dG) ℂ) B] :
    letI := G.incidenceParameterAlgebra a
    Module.Free B (B ⊗[MvPolynomial (Fin G.dG) ℂ] G.IncidenceRing) ∧
      Module.Finite B (B ⊗[MvPolynomial (Fin G.dG) ℂ] G.IncidenceRing) ∧
      Module.FaithfullyFlat B (B ⊗[MvPolynomial (Fin G.dG) ℂ] G.IncidenceRing) ∧
      (Module.finrank B (B ⊗[MvPolynomial (Fin G.dG) ℂ] G.IncidenceRing) : ℤ) =
        G.omegaTilde.eval 1 := by
  letI := G.incidenceParameterAlgebra a
  have h := G.incidence_parameter_finite_free a ha
  haveI : Module.Free (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing := h.1
  haveI : Module.Finite (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing := h.2.1
  haveI : Module.FaithfullyFlat (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing := h.2.2.1
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  rw [Module.finrank_baseChange]
  exact h.2.2.2

/-- Relations in the parameter variables are evaluated in the original incidence ring. -/
noncomputable abbrev incidenceParameterCutIdeal (I : Ideal (MvPolynomial (Fin G.dG) ℂ)) :
    Ideal G.IncidenceRing := I.map (G.incidenceParameterHom a).toRingHom

@[simp] theorem incidenceParameterCutIdeal_eq (I : Ideal (MvPolynomial (Fin G.dG) ℂ)) :
    letI := G.incidenceParameterAlgebra a
    G.incidenceParameterCutIdeal a I =
      I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing) := rfl

/-- The comparison is an algebra equivalence for the original quotient multiplication. -/
noncomputable def incidenceParameterCutEquiv (I : Ideal (MvPolynomial (Fin G.dG) ℂ)) :
    letI := G.incidenceParameterAlgebra a
    (G.IncidenceRing ⧸ I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing)) ≃ₐ[MvPolynomial (Fin G.dG) ℂ ⧸ I]
      (MvPolynomial (Fin G.dG) ℂ ⧸ I) ⊗[MvPolynomial (Fin G.dG) ℂ] G.IncidenceRing := by
  letI := G.incidenceParameterAlgebra a
  exact Algebra.TensorProduct.quotIdealMapEquivQuotTensor G.IncidenceRing I

@[simp] theorem incidenceParameterCutEquiv_mk
    (I : Ideal (MvPolynomial (Fin G.dG) ℂ)) (u : G.IncidenceRing) :
    letI := G.incidenceParameterAlgebra a
    G.incidenceParameterCutEquiv a I
      (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing)) u) =
      1 ⊗ₜ[MvPolynomial (Fin G.dG) ℂ] u := rfl

/-- Every proper parameter cut is finite free of the same rank over its parameter quotient.
The ideal may be nonhomogeneous or nonreduced; this does not identify the different fibers. -/
theorem incidence_parameter_cut_finite_free (ha : a ∈ G.incidenceFiniteParameterLocus)
    (I : Ideal (MvPolynomial (Fin G.dG) ℂ)) (hI : I ≠ ⊤) :
    letI := G.incidenceParameterAlgebra a
    letI : Module (MvPolynomial (Fin G.dG) ℂ ⧸ I)
        (G.IncidenceRing ⧸ I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing)) :=
      @Algebra.toModule (MvPolynomial (Fin G.dG) ℂ ⧸ I)
        (G.IncidenceRing ⧸ I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing))
        inferInstance inferInstance inferInstance
    Module.Free (MvPolynomial (Fin G.dG) ℂ ⧸ I)
        (G.IncidenceRing ⧸ I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing)) ∧
      Module.Finite (MvPolynomial (Fin G.dG) ℂ ⧸ I)
        (G.IncidenceRing ⧸ I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing)) ∧
      Module.FaithfullyFlat (MvPolynomial (Fin G.dG) ℂ ⧸ I)
        (G.IncidenceRing ⧸ I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing)) ∧
      (Module.finrank (MvPolynomial (Fin G.dG) ℂ ⧸ I)
        (G.IncidenceRing ⧸ I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing)) : ℤ) =
        G.omegaTilde.eval 1 := by
  letI := G.incidenceParameterAlgebra a
  letI : Module (MvPolynomial (Fin G.dG) ℂ ⧸ I)
      (G.IncidenceRing ⧸ I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing)) :=
    @Algebra.toModule (MvPolynomial (Fin G.dG) ℂ ⧸ I)
      (G.IncidenceRing ⧸ I.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing))
      inferInstance inferInstance inferInstance
  haveI : Nontrivial (MvPolynomial (Fin G.dG) ℂ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have h := G.incidence_parameter_baseChange a ha (MvPolynomial (Fin G.dG) ℂ ⧸ I)
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2.1
  let e := (G.incidenceParameterCutEquiv a I).toLinearEquiv
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm,
    Module.FaithfullyFlat.of_linearEquiv _ _ e,
    (congrArg (fun n : ℕ => (n : ℤ)) e.finrank_eq).trans h.2.2.2⟩

end BPFixedPoints.Multigraph
