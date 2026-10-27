import BPFixedPoints.Incidence.IncidenceParameterRegular
import BPFixedPoints.Incidence.GradedParameterBasis
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Homogeneous freeness over every finite linear incidence parameter algebra -/

namespace BPFixedPoints.Multigraph

open ResolutionTools MvPolynomial
open scoped PowerSeries TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The polynomial ring acts by the selected actual coefficient forms. -/
@[instance_reducible] noncomputable def incidenceParameterAlgebra (a : G.IncidenceLinearParameters) :
    Algebra (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing :=
  (G.incidenceParameterHom a).toRingHom.toAlgebra

variable (a : G.IncidenceLinearParameters)

noncomputable local instance incParameterFreeGrading :
    GradedAlgebra G.incidenceCoefficientPiece := G.incidenceCoefficientGradedAlgebra

/-- Basis indices retain the degree of the Artin quotient component they come from. -/
abbrev IncidenceParameterBasisIndex :=
  HomogeneousBasisIndex (k := ℂ) (A := G.IncidenceRing ⧸ G.incidenceParameterIdeal a)
    (gradedQuotientPiece G.incidenceCoefficientPiece (G.incidenceParameterIdeal a))

theorem exists_incidenceParameterBasis (ha : a ∈ G.incidenceFiniteParameterLocus) :
    letI := G.incidenceParameterAlgebra a
    ∃ b : Module.Basis (G.IncidenceParameterBasisIndex a)
        (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing,
      ∀ i, b i ∈ G.incidenceCoefficientPiece i.1 := by
  letI := G.incidenceParameterAlgebra a
  haveI : IsScalarTower ℂ (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing :=
    IsScalarTower.of_algHom (G.incidenceParameterHom a)
  haveI : Module.Finite ℂ (G.IncidenceRing ⧸ G.incidenceParameterIdeal a) := ha
  apply exists_homogeneous_parameter_basis G.incidenceCoefficientPiece
    (fun i => by
      rw [show algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing (X i) =
        G.incidenceParameterForm a i from G.incidenceParameterHom_X a i]
      exact G.incidenceParameterForm_mem a i) (G.incidenceParameterIdeal a)
  · apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    exact (G.incidenceParameterHom_X a i).symm
  · rw [G.incidenceParameterHilbertSeries_eq a ha, Fintype.card_fin]
    exact G.incidenceHilbertSeries_eq_omegaTilde

/-- Homogeneous lifts of an actual Artin quotient basis form a polynomial basis. -/
noncomputable def incidenceParameterBasis (ha : a ∈ G.incidenceFiniteParameterLocus) :
    letI := G.incidenceParameterAlgebra a
    Module.Basis (G.IncidenceParameterBasisIndex a)
      (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing :=
  (G.exists_incidenceParameterBasis a ha).choose

theorem incidenceParameterBasis_mem (ha : a ∈ G.incidenceFiniteParameterLocus)
    (i : G.IncidenceParameterBasisIndex a) :
    G.incidenceParameterBasis a ha i ∈ G.incidenceCoefficientPiece i.1 :=
  (G.exists_incidenceParameterBasis a ha).choose_spec i

theorem incidenceParameter_free (ha : a ∈ G.incidenceFiniteParameterLocus) :
    letI := G.incidenceParameterAlgebra a
    Module.Free (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing := by
  letI := G.incidenceParameterAlgebra a
  exact Module.Free.of_basis (G.incidenceParameterBasis a ha)

/-- The polynomial rank is the dimension of the Artin quotient. -/
theorem incidenceParameter_finrank (ha : a ∈ G.incidenceFiniteParameterLocus) :
    letI := G.incidenceParameterAlgebra a
    (Module.finrank (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing : ℤ) = G.omegaTilde.eval 1 := by
  letI := G.incidenceParameterAlgebra a
  haveI : Module.Finite ℂ (G.IncidenceRing ⧸ G.incidenceParameterIdeal a) := ha
  let ℬ := gradedQuotientPiece G.incidenceCoefficientPiece (G.incidenceParameterIdeal a)
  letI : GradedAlgebra (R := ℂ) (A := G.IncidenceRing ⧸ G.incidenceParameterIdeal a) ℬ := gradedQuotientAlgebra _ _ (G.incidenceParameterIdeal_homogeneous a)
  have he : Module.finrank (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing =
      Module.finrank ℂ (G.IncidenceRing ⧸ G.incidenceParameterIdeal a) := by
    rw [Module.finrank_eq_card_basis (G.incidenceParameterBasis a ha),
      Module.finrank_eq_card_basis (homogeneousBasis (k := ℂ) (A := G.IncidenceRing ⧸ G.incidenceParameterIdeal a) ℬ)]
  rw [he]
  exact G.finrank_incidence_parameter_quotient a ha

/-- Every tuple in the open locus gives a finite free, faithfully flat polynomial algebra. -/
theorem incidence_parameter_finite_free (ha : a ∈ G.incidenceFiniteParameterLocus) :
    letI := G.incidenceParameterAlgebra a
    Module.Free (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing ∧
      Module.Finite (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing ∧
      Module.FaithfullyFlat (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing ∧
      (Module.finrank (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing : ℤ) = G.omegaTilde.eval 1 := by
  letI := G.incidenceParameterAlgebra a
  haveI : Module.Free (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing :=
    G.incidenceParameter_free a ha
  haveI : IsDomain G.IncidenceRing := G.incidenceRing_isDomain
  let b := G.incidenceParameterBasis a ha
  haveI : Nonempty (G.IncidenceParameterBasisIndex a) := b.index_nonempty
  haveI : Module.FaithfullyFlat (MvPolynomial (Fin G.dG) ℂ)
      (G.IncidenceParameterBasisIndex a →₀ MvPolynomial (Fin G.dG) ℂ) :=
    Module.FaithfullyFlat.finsupp _ _
  exact ⟨inferInstance, G.incidenceParameterHom_finite a ha,
    Module.FaithfullyFlat.of_linearEquiv _ _ b.repr, G.incidenceParameter_finrank a ha⟩

end BPFixedPoints.Multigraph
