import BPFixedPoints.Incidence.LinearParameterSequence
import BPFixedPoints.Incidence.RegularSequenceHilbert
import BPFixedPoints.Incidence.IncidenceHilbertSeries
import BPFixedPoints.Incidence.FiniteHilbertLength

/-! # The naturally graded Artin quotients of the original incidence ring -/

namespace BPFixedPoints.Multigraph

open ResolutionTools RingTheory.Sequence
open scoped PowerSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance incArtinHilbertGrading :
    GradedAlgebra G.incidenceCoefficientPiece := G.incidenceCoefficientGradedAlgebra

/-- The actual quotient components are the images of the natural ring components. -/
noncomputable def incidenceArtinPiece (rs : List G.IncidenceRing) (q : ℕ) :=
  gradedQuotientPiece G.incidenceCoefficientPiece (Ideal.ofList rs) q

noncomputable instance incidenceArtinPiece_finite (rs : List G.IncidenceRing) (q : ℕ) :
    Module.Finite ℂ (G.incidenceArtinPiece rs q) :=
  gradedQuotientPiece_finite _ _ q

/-- The Artin quotient series, defined by its actual homogeneous dimensions. -/
noncomputable def incidenceArtinHilbertSeries (rs : List G.IncidenceRing) : PowerSeries ℤ :=
  gradedHilbertSeries (k := ℂ) (A := G.IncidenceRing ⧸ Ideal.ofList rs) (G.incidenceArtinPiece rs)

theorem incidence_linear_ideal_homogeneous (rs : List G.IncidenceRing)
    (hh : ∀ x ∈ rs, x ∈ G.incidenceCoefficientPiece 1) :
    (Ideal.ofList rs).IsHomogeneous G.incidenceCoefficientPiece := by
  letI := G.incidenceCoefficientGradedAlgebra
  exact Ideal.homogeneous_span _ _ (fun x hx => ⟨1, hh x hx⟩)

/-- The quotient grading is induced by the original ring, including its multiplication. -/
@[instance_reducible]
noncomputable def incidenceArtinGradedAlgebra (rs : List G.IncidenceRing)
    (hh : ∀ x ∈ rs, x ∈ G.incidenceCoefficientPiece 1) :
    GradedAlgebra (R := ℂ) (A := G.IncidenceRing ⧸ Ideal.ofList rs) (G.incidenceArtinPiece rs) := by
  letI := G.incidenceCoefficientGradedAlgebra
  exact gradedQuotientAlgebra _ _ (G.incidence_linear_ideal_homogeneous rs hh)

theorem incidenceArtinHilbertSeries_eq (rs : List G.IncidenceRing)
    (hlen : rs.length = G.dG) (hh : ∀ x ∈ rs, x ∈ G.incidenceCoefficientPiece 1)
    (hr : IsRegular G.IncidenceRing rs) :
    G.incidenceArtinHilbertSeries rs = (G.omegaTilde : PowerSeries ℤ) := by
  letI := G.incidenceCoefficientGradedAlgebra
  change gradedHilbertSeries (gradedQuotientPiece G.incidenceCoefficientPiece (Ideal.ofList rs)) = _
  rw [gradedHilbertSeries_quotient_regular_sequence _ rs hh hr, hlen]
  change (1 - PowerSeries.X) ^ G.dG * G.incidenceHilbertSeries = _
  rw [G.incidenceHilbertSeries_eq_omegaTilde, mul_left_comm,
    ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
  simp

/-- The dimension of the actual Artin algebra is the value of omega-tilde at one. -/
theorem finrank_incidence_linear_artin (rs : List G.IncidenceRing)
    (hlen : rs.length = G.dG) (hh : ∀ x ∈ rs, x ∈ G.incidenceCoefficientPiece 1)
    (hr : IsRegular G.IncidenceRing rs) :
    (Module.finrank ℂ (G.IncidenceRing ⧸ Ideal.ofList rs) : ℤ) = G.omegaTilde.eval 1 := by
  exact finrank_quotient_eq_eval_one_of_hilbert_polynomial
    G.incidenceCoefficientPiece (Ideal.ofList rs) (G.incidence_linear_ideal_homogeneous rs hh) G.omegaTilde
    (G.incidenceArtinHilbertSeries_eq rs hlen hh hr)

/-- A nonzero finite-dimensional Artin quotient cut out by linear coefficient forms exists,
and its induced Hilbert series is omega-tilde. -/
theorem exists_incidence_linear_artin_hilbert :
    ∃ rs : List (IncCoeffRing E), rs.length = G.dG ∧
      (∀ r ∈ rs, r ∈ MvPolynomial.homogeneousSubmodule (IncCoeffIdx E) ℂ 1) ∧
      IsRegular G.IncidenceRing (rs.map G.coeffHom) ∧
      Ideal.ofList (rs.map G.coeffHom) ≠ ⊤ ∧
      IsArtinianRing (G.IncidenceRing ⧸ Ideal.ofList (rs.map G.coeffHom)) ∧
      Module.Finite ℂ (G.IncidenceRing ⧸ Ideal.ofList (rs.map G.coeffHom)) ∧
      G.incidenceArtinHilbertSeries (rs.map G.coeffHom) = (G.omegaTilde : PowerSeries ℤ) ∧
      (Module.finrank ℂ (G.IncidenceRing ⧸ Ideal.ofList (rs.map G.coeffHom)) : ℤ) =
        G.omegaTilde.eval 1 := by
  obtain ⟨rs, hlen, hh, hr, hn, ha, hf⟩ := G.exists_incidence_linear_artin_quotient
  have hh' : ∀ x ∈ rs.map G.coeffHom, x ∈ G.incidenceCoefficientPiece 1 := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact G.coeffHom_coefficient_degree (hh r hr)
  exact ⟨rs, hlen, hh, hr, hn, ha, hf,
    G.incidenceArtinHilbertSeries_eq _ (by simpa using hlen) hh' hr,
    G.finrank_incidence_linear_artin _ (by simpa using hlen) hh' hr⟩

end BPFixedPoints.Multigraph
