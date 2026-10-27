import BPFixedPoints.Incidence.IncidenceParameterOpen
import BPFixedPoints.Incidence.GradedParameterFinite
import BPFixedPoints.Incidence.ParameterIndependence

/-! # Every finite linear incidence quotient determines a polynomial normalization -/

namespace BPFixedPoints.Multigraph

open ResolutionTools MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance incParameterNormalizationGrading :
    GradedAlgebra G.incidenceCoefficientPiece := G.incidenceCoefficientGradedAlgebra

/-- The polynomial parameter algebra acts by the selected actual linear forms. -/
noncomputable def incidenceParameterHom (a : G.IncidenceLinearParameters) :
    MvPolynomial (Fin G.dG) ℂ →ₐ[ℂ] G.IncidenceRing := aeval (G.incidenceParameterForm a)

@[simp] theorem incidenceParameterHom_X (a : G.IncidenceLinearParameters) (i : Fin G.dG) :
    G.incidenceParameterHom a (X i) = G.incidenceParameterForm a i := aeval_X _ _

/-- Every tuple in the finite-quotient locus makes the original ring finite over its parameters. -/
theorem incidenceParameterHom_finite (a : G.IncidenceLinearParameters)
    (ha : a ∈ G.incidenceFiniteParameterLocus) : (G.incidenceParameterHom a).toRingHom.Finite := by
  let T := MvPolynomial (Fin G.dG) ℂ
  letI : Algebra T G.IncidenceRing := (G.incidenceParameterHom a).toRingHom.toAlgebra
  haveI : IsScalarTower ℂ T G.IncidenceRing := IsScalarTower.of_algHom (G.incidenceParameterHom a)
  have he : (fun i => algebraMap T G.IncidenceRing (X i)) = G.incidenceParameterForm a := by
    funext i
    exact G.incidenceParameterHom_X a i
  haveI : Module.Finite ℂ (G.IncidenceRing ⧸
      Ideal.span (Set.range (fun i => algebraMap T G.IncidenceRing (X i)))) := by
    rw [he]
    exact ha
  exact finite_over_parameters_of_finite_quotient G.incidenceCoefficientPiece X
    (fun i => by rw [show algebraMap T G.IncidenceRing (X i) = G.incidenceParameterForm a i from
      G.incidenceParameterHom_X a i]; exact G.incidenceParameterForm_mem a i)

/-- Full dimension rules out polynomial relations between the selected parameters. -/
theorem incidenceParameterHom_injective (a : G.IncidenceLinearParameters)
    (ha : a ∈ G.incidenceFiniteParameterLocus) : Function.Injective (G.incidenceParameterHom a) :=
  polynomial_finite_injective_of_dimension G.dG (G.incidenceParameterHom a)
    (G.incidenceParameterHom_finite a ha) G.incidenceRing_krullDim

theorem incidenceParameterForm_algebraicIndependent (a : G.IncidenceLinearParameters)
    (ha : a ∈ G.incidenceFiniteParameterLocus) : AlgebraicIndependent ℂ (G.incidenceParameterForm a) :=
  algebraicIndependent_iff_injective_aeval.mpr (G.incidenceParameterHom_injective a ha)

/-- Every point of the open locus gives a finite injective polynomial normalization.
Regularity is proved in `IncidenceParameterRegular`; homogeneous freeness is proved in
`IncidenceParameterFree`. -/
theorem incidence_parameter_normalization (a : G.IncidenceLinearParameters)
    (ha : a ∈ G.incidenceFiniteParameterLocus) :
    (G.incidenceParameterHom a).toRingHom.Finite ∧
      Function.Injective (G.incidenceParameterHom a) ∧
      AlgebraicIndependent ℂ (G.incidenceParameterForm a) :=
  ⟨G.incidenceParameterHom_finite a ha, G.incidenceParameterHom_injective a ha,
    G.incidenceParameterForm_algebraicIndependent a ha⟩

end BPFixedPoints.Multigraph
