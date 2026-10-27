import BPFixedPoints.Incidence.LinearPolynomialCoordinates
import BPFixedPoints.Incidence.IncidenceParameterFree
import Mathlib.RingTheory.AlgebraTower

/-! # The original coefficient ring over the selected incidence parameters -/

namespace BPFixedPoints.Multigraph

open ResolutionTools MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (a : G.IncidenceLinearParameters)

noncomputable local instance coefficientParametersAlgebra :
    Algebra (IncCoeffRing E) G.IncidenceRing := G.coeffHom.toRingHom.toAlgebra

/-- Coefficient vectors of the specified forms, in the original coefficient variables. -/
noncomputable def incidenceCoefficientParameterVector (i : Fin G.dG) : IncCoeffIdx E →₀ ℂ :=
  Finsupp.equivFunOnFinite.symm (fun j => a (i, j))

theorem incidenceCoefficientParameterVector_form (i : Fin G.dG) :
    polynomialLinearForm (G.incidenceCoefficientParameterVector a i) =
      linearParameterForm (X : IncCoeffIdx E → IncCoeffRing E) a i := by
  classical
  simp [polynomialLinearForm, Finsupp.linearCombination_apply, Finsupp.sum_fintype,
    incidenceCoefficientParameterVector, linearParameterForm]

/-- Independence in the incidence ring implies independence of the coefficient vectors. -/
theorem incidenceCoefficientParameterVector_independent
    (ha : a ∈ G.incidenceFiniteParameterLocus) :
    LinearIndependent ℂ (G.incidenceCoefficientParameterVector a) := by
  let f := G.coeffHom.toLinearMap.comp (Finsupp.linearCombination ℂ X)
  apply LinearIndependent.of_comp f
  have he : f ∘ G.incidenceCoefficientParameterVector a = G.incidenceParameterForm a := by
    funext i
    change G.coeffHom (polynomialLinearForm (G.incidenceCoefficientParameterVector a i)) = _
    rw [G.incidenceCoefficientParameterVector_form, G.incidenceParameterForm_eq]
  rw [he]
  exact (G.incidenceParameterForm_algebraicIndependent a ha).linearIndependent

/-- The parameter action on the coefficient ring evaluates the same linear forms. -/
@[instance_reducible] noncomputable def incidenceCoefficientParameterAlgebra :
    Algebra (MvPolynomial (Fin G.dG) ℂ) (IncCoeffRing E) :=
  linearPolynomialAlgebra (G.incidenceCoefficientParameterVector a)

theorem incidenceCoefficientParameter_tower :
    letI := G.incidenceCoefficientParameterAlgebra a
    letI := G.incidenceParameterAlgebra a
    IsScalarTower (MvPolynomial (Fin G.dG) ℂ) (IncCoeffRing E) G.IncidenceRing := by
  letI := G.incidenceCoefficientParameterAlgebra a
  letI := G.incidenceParameterAlgebra a
  apply IsScalarTower.of_algebraMap_eq'
  have he : G.incidenceParameterHom a =
      G.coeffHom.comp (aeval (polynomialLinearForm ∘ G.incidenceCoefficientParameterVector a)) := by
    ext i
    simp only [AlgHom.comp_apply, aeval_X, Function.comp_apply,
      G.incidenceParameterHom_X, G.incidenceCoefficientParameterVector_form]
    exact congrArg Subtype.val (G.incidenceParameterForm_eq a i)
  exact congrArg AlgHom.toRingHom he

/-- Coordinates extending the parameters make the coefficient ring a polynomial algebra over T. -/
noncomputable def incidenceCoefficientParameterEquiv (ha : a ∈ G.incidenceFiniteParameterLocus) :
    letI := G.incidenceCoefficientParameterAlgebra a
    IncCoeffRing E ≃ₐ[MvPolynomial (Fin G.dG) ℂ]
      MvPolynomial (Module.Basis.sumExtendIndex (G.incidenceCoefficientParameterVector_independent a ha))
        (MvPolynomial (Fin G.dG) ℂ) :=
  linearPolynomialParameterEquiv (G.incidenceCoefficientParameterVector_independent a ha)

theorem incidenceCoefficientParameter_free (ha : a ∈ G.incidenceFiniteParameterLocus) :
    letI := G.incidenceCoefficientParameterAlgebra a
    Module.Free (MvPolynomial (Fin G.dG) ℂ) (IncCoeffRing E) :=
  free_over_linear_parameters (G.incidenceCoefficientParameterVector_independent a ha)

end BPFixedPoints.Multigraph
