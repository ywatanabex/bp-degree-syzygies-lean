import BPFixedPoints.Incidence.IncidenceParameterNormalization
import BPFixedPoints.Incidence.GradedFiniteRadical
import BPFixedPoints.Incidence.ConnectedGradedMaximal
import BPFixedPoints.Incidence.DepthRadical

/-! # The radical and depth of every finite linear incidence parameter ideal -/

namespace BPFixedPoints.Multigraph

open ResolutionTools CategoryTheory RingTheory.Sequence
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance incParameterDepthGrading :
    GradedAlgebra G.incidenceCoefficientPiece := G.incidenceCoefficientGradedAlgebra
local instance incParameterDepthNoetherian : IsNoetherianRing G.IncidenceRing :=
  G.incidence_cohenMacaulay.1

/-- The positive-degree ideal of the original naturally graded incidence ring. -/
noncomputable def incidencePositiveIdeal : Ideal G.IncidenceRing :=
  (HomogeneousIdeal.irrelevant G.incidenceCoefficientPiece).toIdeal

theorem incidencePositiveIdeal_isMaximal : G.incidencePositiveIdeal.IsMaximal :=
  irrelevant_isMaximal_of_degree_zero G.incidenceCoefficientPiece
    (fun x hx => (G.mem_incidenceCoefficientPiece_zero x).mp hx)

theorem incidenceParameterIdeal_le_positive (a : G.IncidenceLinearParameters) :
    G.incidenceParameterIdeal a ≤ G.incidencePositiveIdeal := by
  apply Ideal.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact HomogeneousIdeal.mem_irrelevant_of_mem _ (Nat.zero_lt_one)
    (G.incidenceParameterForm_mem a i)

/-- Every finite linear quotient is supported at the homogeneous origin. -/
theorem incidenceParameterIdeal_radical (a : G.IncidenceLinearParameters)
    (ha : a ∈ G.incidenceFiniteParameterLocus) :
    (G.incidenceParameterIdeal a).radical = G.incidencePositiveIdeal := by
  have : Module.Finite ℂ (G.IncidenceRing ⧸ G.incidenceParameterIdeal a) := ha
  exact radical_eq_irrelevant_of_finite_quotient G.incidenceCoefficientPiece
    (G.incidenceParameterIdeal a) (G.incidenceParameterIdeal_homogeneous a)
    (G.incidenceParameterIdeal_le_positive a)

/-- The positive-degree ideal has depth d_G on the original ring. -/
theorem incidencePositiveIdeal_depth :
    G.incidencePositiveIdeal.depth (ModuleCat.of G.IncidenceRing G.IncidenceRing) = (G.dG : ℕ∞) := by
  have hp : G.incidencePositiveIdeal • (⊤ : Ideal G.IncidenceRing) < ⊤ := by
    simpa using G.incidencePositiveIdeal_isMaximal.lt_top
  apply le_antisymm
  · apply depth_le_of_supportDim_le _ (ModuleCat.of G.IncidenceRing G.IncidenceRing) hp G.dG
    rw [Module.supportDim_self_eq_ringKrullDim, G.incidenceRing_krullDim]
  · obtain ⟨rs, hlen, hh, hr, _⟩ := G.exists_incidence_linear_artin_quotient
    rw [Ideal.depth_eq_sSup_length_isRegular _ (ModuleCat.of G.IncidenceRing G.IncidenceRing) hp]
    apply le_sSup
    refine ⟨rs.map G.coeffHom, hr, ?_, ?_⟩
    · intro x hx
      obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp hx
      exact HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one
        (G.coeffHom_coefficient_degree (hh r hmem))
    · simp [hlen]

/-- Every ideal in the finite-quotient locus has depth equal to the number of parameters.
The generator-wise regular-sequence criterion is a separate statement. -/
theorem incidenceParameterIdeal_depth (a : G.IncidenceLinearParameters)
    (ha : a ∈ G.incidenceFiniteParameterLocus) :
    (G.incidenceParameterIdeal a).depth (ModuleCat.of G.IncidenceRing G.IncidenceRing) =
      (G.dG : ℕ∞) := by
  have hp : G.incidencePositiveIdeal • (⊤ : Ideal G.IncidenceRing) < ⊤ := by
    simpa using G.incidencePositiveIdeal_isMaximal.lt_top
  have hi : G.incidenceParameterIdeal a • (⊤ : Ideal G.IncidenceRing) < ⊤ := by
    simpa using (G.incidenceParameterIdeal_ne_top a).lt_top
  rw [depth_eq_of_radical_eq (G.incidenceParameterIdeal a) G.incidencePositiveIdeal
    (ModuleCat.of G.IncidenceRing G.IncidenceRing) hi hp
    ((G.incidenceParameterIdeal_radical a ha).trans G.incidencePositiveIdeal_isMaximal.isPrime.radical.symm)]
  exact G.incidencePositiveIdeal_depth

end BPFixedPoints.Multigraph
