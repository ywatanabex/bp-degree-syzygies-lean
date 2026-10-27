import BPFixedPoints.Incidence.LinearArtinHilbert
import BPFixedPoints.Incidence.PolynomialLinearCoordinates
import BPFixedPoints.Incidence.ParameterZariski
import BPFixedPoints.Incidence.FiniteGradedBound

/-! # A nonempty principal open set of finite incidence quotients -/

namespace BPFixedPoints.Multigraph

open ResolutionTools MvPolynomial
open scoped PowerSeries
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance incParameterOpenAlgebra : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra
noncomputable local instance incParameterOpenFinite : Module.Finite (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom_finite
noncomputable local instance incParameterOpenTower : IsScalarTower ℂ (IncCoeffRing E) G.IncidenceRing :=
  IsScalarTower.of_algHom G.coeffHom
noncomputable local instance incParameterOpenGrading : GradedAlgebra G.incidenceCoefficientPiece :=
  G.incidenceCoefficientGradedAlgebra

/-- Coordinates of a tuple of d_G linear coefficient forms. -/
abbrev IncidenceLinearParameters := Fin G.dG × IncCoeffIdx E → ℂ

/-- The actual elements of the original ring specified by a coefficient tuple. -/
noncomputable def incidenceParameterForm (a : G.IncidenceLinearParameters) (i : Fin G.dG) :
    G.IncidenceRing := linearParameterForm (fun j => G.coeffHom (X j)) a i

noncomputable def incidenceParameterIdeal (a : G.IncidenceLinearParameters) : Ideal G.IncidenceRing :=
  Ideal.span (Set.range (G.incidenceParameterForm a))

theorem incidenceParameterForm_mem (a : G.IncidenceLinearParameters) (i : Fin G.dG) :
    G.incidenceParameterForm a i ∈ G.incidenceCoefficientPiece 1 :=
  linearParameterForm_mem _ _ (fun j => G.coeffHom_coefficient_degree (isHomogeneous_X ℂ j)) a i

theorem incidenceParameterForm_eq (a : G.IncidenceLinearParameters) (i : Fin G.dG) :
    G.incidenceParameterForm a i = G.coeffHom (linearParameterForm X a i) := by
  simp [incidenceParameterForm, linearParameterForm]

/-- Every such quotient is nonzero: all linear parameters vanish at the coefficient origin. -/
theorem incidenceParameterIdeal_ne_top (a : G.IncidenceLinearParameters) :
    G.incidenceParameterIdeal a ≠ ⊤ := by
  have h : G.incidenceParameterIdeal a ≤ RingHom.ker G.incidenceOrigin.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change G.incidenceOrigin (G.incidenceParameterForm a i) = 0
    simp [incidenceParameterForm_eq, linearParameterForm]
  intro ht
  exact RingHom.ker_ne_top G.incidenceOrigin.toRingHom (top_unique (ht ▸ h))

/-- A polynomial nonvanishing condition guarantees finite-dimensional, nonzero Artin quotients.
This theorem does not assert regularity of every tuple on the resulting open set. -/
theorem exists_incidence_parameter_certificate :
    ∃ P : MvPolynomial (Fin G.dG × IncCoeffIdx E) ℂ,
      (∃ a : G.IncidenceLinearParameters, eval a P ≠ 0) ∧
      ∀ a : G.IncidenceLinearParameters, eval a P ≠ 0 →
        G.incidenceParameterIdeal a ≠ ⊤ ∧
        Module.Finite ℂ (G.IncidenceRing ⧸ G.incidenceParameterIdeal a) ∧
        IsArtinianRing (G.IncidenceRing ⧸ G.incidenceParameterIdeal a) := by
  classical
  obtain ⟨rs, hlen, hh, _, _, _, _, hH, _⟩ := G.exists_incidence_linear_artin_hilbert
  obtain ⟨a, ha⟩ := exists_linearParameterForm_list rs G.dG hlen hh
  have hl : List.ofFn (G.incidenceParameterForm a) = rs.map G.coeffHom := by
    rw [show G.incidenceParameterForm a = G.coeffHom ∘ linearParameterForm X a from
      funext (G.incidenceParameterForm_eq a)]
    rw [← List.map_ofFn, ha]
  have hI : G.incidenceParameterIdeal a = Ideal.ofList (rs.map G.coeffHom) := by
    rw [← hl, ideal_ofList_ofFn]
    rfl
  let q := G.omegaTilde.natDegree
  have hz : gradedQuotientPiece G.incidenceCoefficientPiece
      (G.incidenceParameterIdeal a) (q + 1) = ⊥ := by
    rw [hI]
    have hc := congrArg (PowerSeries.coeff (q + 1)) hH
    have hq : G.omegaTilde.coeff (q + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
    simp only [incidenceArtinHilbertSeries, gradedHilbertSeries, PowerSeries.coeff_mk,
      Polynomial.coeff_coe, hq, Nat.cast_eq_zero] at hc
    exact Submodule.finrank_eq_zero.mp hc
  have hs := linearSequenceMultiply_surjective_of_piece_zero G.incidenceCoefficientPiece
    (G.incidenceParameterForm a) (G.incidenceParameterForm_mem a) q hz
  obtain ⟨P, hp, hb⟩ := exists_linearParameter_surjectivity_certificate G.incidenceCoefficientPiece
    (fun j => G.coeffHom (X j)) (fun j => G.coeffHom_coefficient_degree (isHomogeneous_X ℂ j)) q a hs
  refine ⟨P, ⟨a, hp⟩, fun b hp => ⟨G.incidenceParameterIdeal_ne_top b, ?_⟩⟩
  exact finite_quotient_of_linearSequenceMultiply_surjective G.incidenceCoefficientPiece
    (fun j => G.coeffHom_coefficient_degree (isHomogeneous_X ℂ j))
    (G.incidenceParameterForm b) (G.incidenceParameterForm_mem b) q (hb b hp)

/-- The full locus where the actual linear quotient is finite-dimensional. -/
def incidenceFiniteParameterLocus : Set G.IncidenceLinearParameters :=
  {a | Module.Finite ℂ (G.IncidenceRing ⧸ G.incidenceParameterIdeal a)}

theorem incidenceParameterIdeal_homogeneous (a : G.IncidenceLinearParameters) :
    (G.incidenceParameterIdeal a).IsHomogeneous G.incidenceCoefficientPiece := by
  apply Ideal.homogeneous_span
  rintro x ⟨i, rfl⟩
  exact ⟨1, G.incidenceParameterForm_mem a i⟩

/-- The entire finite-dimensional quotient locus is Zariski open, not just a chosen subset. -/
theorem isOpen_incidenceFiniteParameterLocus :
    IsOpen[parameterZariskiTopology] G.incidenceFiniteParameterLocus := by
  letI : TopologicalSpace G.IncidenceLinearParameters := parameterZariskiTopology
  refine isOpen_iff_forall_mem_open.mpr (fun a ha => ?_)
  have : Module.Finite ℂ (G.IncidenceRing ⧸ G.incidenceParameterIdeal a) := ha
  obtain ⟨q, hz⟩ := exists_gradedQuotientPiece_zero G.incidenceCoefficientPiece
    (G.incidenceParameterIdeal a) (G.incidenceParameterIdeal_homogeneous a)
  have hs := linearSequenceMultiply_surjective_of_piece_zero G.incidenceCoefficientPiece
    (G.incidenceParameterForm a) (G.incidenceParameterForm_mem a) q hz
  obtain ⟨P, hp, hb⟩ := exists_linearParameter_surjectivity_certificate G.incidenceCoefficientPiece
    (fun j => G.coeffHom (X j)) (fun j => G.coeffHom_coefficient_degree (isHomogeneous_X ℂ j)) q a hs
  refine ⟨{b | eval b P ≠ 0}, fun b h => ?_, isOpen_parameter_nonvanishing P, hp⟩
  exact (finite_quotient_of_linearSequenceMultiply_surjective G.incidenceCoefficientPiece
    (fun j => G.coeffHom_coefficient_degree (isHomogeneous_X ℂ j))
    (G.incidenceParameterForm b) (G.incidenceParameterForm_mem b) q (hb b h)).1

/-- A nonempty Zariski-open locus of nonzero finite-dimensional Artin quotients. -/
theorem incidence_finite_parameter_open :
    IsOpen[parameterZariskiTopology] G.incidenceFiniteParameterLocus ∧
      G.incidenceFiniteParameterLocus.Nonempty ∧
      ∀ a ∈ G.incidenceFiniteParameterLocus,
        G.incidenceParameterIdeal a ≠ ⊤ ∧
        IsArtinianRing (G.IncidenceRing ⧸ G.incidenceParameterIdeal a) := by
  obtain ⟨P, ⟨a, ha⟩, hb⟩ := G.exists_incidence_parameter_certificate
  refine ⟨G.isOpen_incidenceFiniteParameterLocus, ⟨a, (hb a ha).2.1⟩, fun b h => ?_⟩
  have : Module.Finite ℂ (G.IncidenceRing ⧸ G.incidenceParameterIdeal b) := h
  exact ⟨G.incidenceParameterIdeal_ne_top b, IsArtinianRing.of_finite ℂ _⟩

end BPFixedPoints.Multigraph
