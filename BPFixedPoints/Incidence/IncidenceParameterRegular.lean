import BPFixedPoints.Incidence.IncidenceParameterDepth
import BPFixedPoints.Incidence.GradedDepthCriterion

/-! # Regularity and constant Hilbert series on the full finite-parameter locus -/

namespace BPFixedPoints.Multigraph

open ResolutionTools CategoryTheory RingTheory.Sequence
open scoped PowerSeries Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance incParameterRegularGrading :
    GradedAlgebra G.incidenceCoefficientPiece := G.incidenceCoefficientGradedAlgebra
local instance incParameterRegularNoetherian : IsNoetherianRing G.IncidenceRing :=
  G.incidence_cohenMacaulay.1

/-- The parameter tuple in its specified order. -/
noncomputable def incidenceParameterList (a : G.IncidenceLinearParameters) : List G.IncidenceRing :=
  List.ofFn (G.incidenceParameterForm a)

@[simp] theorem incidenceParameterList_length (a : G.IncidenceLinearParameters) :
    (G.incidenceParameterList a).length = G.dG := List.length_ofFn

theorem incidenceParameterList_mem (a : G.IncidenceLinearParameters) :
    ∀ x ∈ G.incidenceParameterList a, x ∈ G.incidenceCoefficientPiece 1 := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact G.incidenceParameterForm_mem a i

theorem incidenceParameterList_ideal (a : G.IncidenceLinearParameters) :
    Ideal.ofList (G.incidenceParameterList a) = G.incidenceParameterIdeal a := by
  apply congrArg Ideal.span
  ext x
  simp [incidenceParameterList, List.mem_ofFn]

/-- Every tuple giving a finite-dimensional quotient is itself a regular sequence. -/
theorem incidenceParameterList_regular (a : G.IncidenceLinearParameters)
    (ha : a ∈ G.incidenceFiniteParameterLocus) :
    IsRegular G.IncidenceRing (G.incidenceParameterList a) := by
  apply regular_of_depth_ge_length G.incidenceCoefficientPiece _ (G.incidenceParameterList_mem a)
  · rw [G.incidenceParameterList_ideal]
    exact G.incidenceParameterIdeal_ne_top a
  · rw [G.incidenceParameterList_length, G.incidenceParameterList_ideal,
      G.incidenceParameterIdeal_depth a ha]

/-- The Hilbert series of the actual induced quotient grading is constant on the open locus. -/
theorem incidenceParameterHilbertSeries_eq (a : G.IncidenceLinearParameters)
    (ha : a ∈ G.incidenceFiniteParameterLocus) :
    gradedHilbertSeries (k := ℂ) (A := G.IncidenceRing ⧸ G.incidenceParameterIdeal a)
      (gradedQuotientPiece G.incidenceCoefficientPiece
      (G.incidenceParameterIdeal a)) = (G.omegaTilde : PowerSeries ℤ) := by
  rw [← G.incidenceParameterList_ideal]
  exact G.incidenceArtinHilbertSeries_eq _ (G.incidenceParameterList_length a)
    (G.incidenceParameterList_mem a) (G.incidenceParameterList_regular a ha)

/-- Every point of the finite-quotient locus has the same quotient dimension. -/
theorem finrank_incidence_parameter_quotient (a : G.IncidenceLinearParameters)
    (ha : a ∈ G.incidenceFiniteParameterLocus) :
    (Module.finrank ℂ (G.IncidenceRing ⧸ G.incidenceParameterIdeal a) : ℤ) =
      G.omegaTilde.eval 1 := by
  rw [← G.incidenceParameterList_ideal]
  exact G.finrank_incidence_linear_artin _ (G.incidenceParameterList_length a)
    (G.incidenceParameterList_mem a) (G.incidenceParameterList_regular a ha)

/-- The complete open-locus statement for the original chart-intersection ring.
No connectedness or looplessness hypothesis is needed for these algebraic conclusions. -/
theorem incidence_parameter_regular_open :
    IsOpen[parameterZariskiTopology] G.incidenceFiniteParameterLocus ∧
    G.incidenceFiniteParameterLocus.Nonempty ∧
    ∀ a ∈ G.incidenceFiniteParameterLocus,
      IsRegular G.IncidenceRing (G.incidenceParameterList a) ∧
      G.incidenceParameterIdeal a ≠ ⊤ ∧
      IsArtinianRing (G.IncidenceRing ⧸ G.incidenceParameterIdeal a) ∧
      gradedHilbertSeries (k := ℂ) (A := G.IncidenceRing ⧸ G.incidenceParameterIdeal a)
        (gradedQuotientPiece G.incidenceCoefficientPiece
        (G.incidenceParameterIdeal a)) = (G.omegaTilde : PowerSeries ℤ) ∧
      (Module.finrank ℂ (G.IncidenceRing ⧸ G.incidenceParameterIdeal a) : ℤ) =
        G.omegaTilde.eval 1 := by
  obtain ⟨ho, hn, ha⟩ := G.incidence_finite_parameter_open
  exact ⟨ho, hn, fun a h => ⟨G.incidenceParameterList_regular a h,
    (ha a h).1, (ha a h).2, G.incidenceParameterHilbertSeries_eq a h,
    G.finrank_incidence_parameter_quotient a h⟩⟩

end BPFixedPoints.Multigraph
