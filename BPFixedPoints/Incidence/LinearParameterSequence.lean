import BPFixedPoints.Incidence.PolynomialLinearIdeal
import BPFixedPoints.Incidence.RegularSequenceInSubspace
import BPFixedPoints.Incidence.IncidenceArtin
import BPFixedPoints.Incidence.NaturalGradedResolution

/-! # Homogeneous linear regular sequences on the original incidence module -/

namespace BPFixedPoints.Multigraph

open ResolutionTools MvPolynomial RingTheory.Sequence CategoryTheory
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance incLinearParameterAlgebra : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra
noncomputable local instance incLinearParameterFinite : Module.Finite (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom_finite

/-- Homogeneous linear coefficient forms give a regular sequence of length d_G. -/
theorem exists_incidence_linear_regular_sequence :
    ∃ rs : List (IncCoeffRing E), rs.length = G.dG ∧
      (∀ r ∈ rs, r ∈ MvPolynomial.homogeneousSubmodule (IncCoeffIdx E) ℂ 1) ∧
      IsRegular G.IncidenceRing rs := by
  apply exists_regular_sequence_in_subspace
    (MvPolynomial.homogeneousSubmodule (IncCoeffIdx E) ℂ 1)
    (incCoeffAugmentationIdeal E) ideal_span_homogeneous_one_eq_ker_constantCoeff
    G.dG (ModuleCat.of (IncCoeffRing E) G.IncidenceRing) G.incCoeffAugmentation_smul_lt_top
  exact le_of_eq G.incidenceDepth_eq.symm

/-- The images of the chosen coefficient forms are regular on the original ring. -/
theorem incidence_linear_sequence_map_regular (rs : List (IncCoeffRing E))
    (hr : IsRegular G.IncidenceRing rs) : IsRegular G.IncidenceRing (rs.map G.coeffHom) := by
  apply (AddEquiv.isRegular_congr (e := AddEquiv.refl G.IncidenceRing) ?_).mp hr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro r _ x
  rfl

/-- A homogeneous linear regular sequence gives a nonzero finite-dimensional Artin quotient. -/
theorem exists_incidence_linear_artin_quotient :
    ∃ rs : List (IncCoeffRing E), rs.length = G.dG ∧
      (∀ r ∈ rs, r ∈ MvPolynomial.homogeneousSubmodule (IncCoeffIdx E) ℂ 1) ∧
      IsRegular G.IncidenceRing (rs.map G.coeffHom) ∧
      Ideal.ofList (rs.map G.coeffHom) ≠ ⊤ ∧
      IsArtinianRing (G.IncidenceRing ⧸ Ideal.ofList (rs.map G.coeffHom)) ∧
      Module.Finite ℂ (G.IncidenceRing ⧸ Ideal.ofList (rs.map G.coeffHom)) := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := G.exists_incidence_linear_regular_sequence
  have hr := G.incidence_linear_sequence_map_regular rs hreg
  exact ⟨rs, hlen, hmem, hr, regular_ideal_ofList_ne_top _ hr,
    G.incidence_regular_quotient_artinian _ (by simpa using hlen) hr⟩

end BPFixedPoints.Multigraph
