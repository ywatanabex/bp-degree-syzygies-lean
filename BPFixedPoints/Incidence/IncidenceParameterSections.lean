import BPFixedPoints.Incidence.IncidenceParameterRegular

/-! # Hilbert series of partial linear parameter sections -/

namespace BPFixedPoints.ResolutionTools

open RingTheory.Sequence
open scoped Pointwise

/-- Every initial segment of a regular sequence on a ring is regular. -/
theorem regular_take {A : Type*} [CommRing A] {rs : List A}
    (hr : IsRegular A rs) (r : ℕ) : IsRegular A (rs.take r) := by
  have hw : IsWeaklyRegular A (rs.take r ++ rs.drop r) := by
    simpa only [List.take_append_drop] using hr.toIsWeaklyRegular
  refine ⟨((isWeaklyRegular_append_iff A _ _).mp hw).1, ?_⟩
  have hle : Ideal.ofList (rs.take r) ≤ Ideal.ofList rs :=
    Ideal.span_mono (fun _ hx => List.mem_of_mem_take hx)
  have hproper : Ideal.ofList rs ≠ ⊤ := by simpa [ne_comm] using hr.top_ne_smul
  have hproper' : Ideal.ofList (rs.take r) ≠ ⊤ := ne_top_of_le_ne_top hproper hle
  simpa [ne_comm] using hproper'

end BPFixedPoints.ResolutionTools

namespace BPFixedPoints.Multigraph

open ResolutionTools RingTheory.Sequence
open scoped PowerSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (a : G.IncidenceLinearParameters)

noncomputable local instance incParameterSectionGrading :
    GradedAlgebra G.incidenceCoefficientPiece := G.incidenceCoefficientGradedAlgebra

/-- The ideal of the first r selected actual coefficient forms. -/
noncomputable abbrev incidenceParameterSectionIdeal (r : ℕ) : Ideal G.IncidenceRing :=
  Ideal.ofList ((G.incidenceParameterList a).take r)

theorem incidenceParameterSection_regular (ha : a ∈ G.incidenceFiniteParameterLocus) (r : ℕ) :
    IsRegular G.IncidenceRing ((G.incidenceParameterList a).take r) :=
  regular_take (G.incidenceParameterList_regular a ha) r

/-- Each partial quotient has the original induced grading and the remaining denominator. -/
theorem incidenceParameterSection_hilbert (ha : a ∈ G.incidenceFiniteParameterLocus)
    (r : ℕ) (hr : r ≤ G.dG) :
    gradedHilbertSeries (k := ℂ) (A := G.IncidenceRing ⧸ G.incidenceParameterSectionIdeal a r)
      (gradedQuotientPiece G.incidenceCoefficientPiece (G.incidenceParameterSectionIdeal a r)) =
      (G.omegaTilde : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (G.dG - r)).val := by
  rw [gradedHilbertSeries_quotient_regular_sequence G.incidenceCoefficientPiece _
    (fun x hx => G.incidenceParameterList_mem a x (List.mem_of_mem_take hx))
    (G.incidenceParameterSection_regular a ha r)]
  rw [List.length_take, G.incidenceParameterList_length, Nat.min_eq_left hr]
  change (1 - PowerSeries.X) ^ r * G.incidenceHilbertSeries = _
  rw [G.incidenceHilbertSeries_eq_omegaTilde, mul_left_comm]
  congr 1
  have he : G.dG = (G.dG - r) + r := (Nat.sub_add_cancel hr).symm
  rw [he, PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val]
  simp only [Nat.add_sub_cancel]

/-- The one-dimensional section has numerator omega-tilde and denominator 1-t. -/
theorem incidenceParameterPencil_hilbert (ha : a ∈ G.incidenceFiniteParameterLocus)
    (hd : 0 < G.dG) :
    gradedHilbertSeries (k := ℂ)
      (A := G.IncidenceRing ⧸ G.incidenceParameterSectionIdeal a (G.dG - 1))
      (gradedQuotientPiece G.incidenceCoefficientPiece
        (G.incidenceParameterSectionIdeal a (G.dG - 1))) =
      (G.omegaTilde : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ 1).val := by
  have h := G.incidenceParameterSection_hilbert a ha (G.dG - 1) (Nat.sub_le _ _)
  rwa [show G.dG - (G.dG - 1) = 1 by omega] at h

end BPFixedPoints.Multigraph
