import BPFixedPoints.Incidence.IncidenceCutTorNaturality

/-! # Multiplicative comparisons among successive linear sections

These are the actual parameter-quotient Tor spaces, including the original,
pencil and Artin sections. Naturality on all free representatives is the
quotient-map theorem `incidenceCutTorComparison_natural`.
-/

namespace BPFixedPoints.Multigraph
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (a : G.IncidenceLinearParameters)
  (ha : a ∈ G.incidenceFiniteParameterLocus)

/-- More successive coordinate cuts give a larger actual parameter ideal. -/
theorem incidenceParameterCoordinateIdeal_mono {r s : ℕ} (hrs : r ≤ s) :
    G.incidenceParameterCoordinateIdeal r ≤ G.incidenceParameterCoordinateIdeal s := by
  apply Ideal.span_mono
  intro x hx
  have ht : (List.ofFn (X : Fin G.dG → MvPolynomial (Fin G.dG) ℂ)).take r =
      ((List.ofFn (X : Fin G.dG → MvPolynomial (Fin G.dG) ℂ)).take s).take r := by
    rw [List.take_take, Nat.min_eq_left hrs]
  rw [ht] at hx
  exact List.mem_of_mem_take hx

/-- Actual scalar-extension multiplication for the first r linear cuts. -/
noncomputable def incidenceSectionTorProduct (r p q : ℕ) :
    G.incidenceSectionTor a r p →ₗ[ℂ] G.incidenceSectionTor a r q →ₗ[ℂ]
      G.incidenceSectionTor a r (p+q) :=
  G.incidenceCutTorProduct a (G.incidenceParameterCoordinateIdeal r)
    (G.incidenceParameterCoordinateIdeal_origin r) ha p q

/-- The comparison between any two successive sections. For r≤s it is induced
by the actual coefficient quotient, as proved by the general naturality theorem. -/
noncomputable def incidenceSectionTorComparison (r s p : ℕ) :
    G.incidenceSectionTor a r p ≃ₗ[ℂ] G.incidenceSectionTor a s p :=
  G.incidenceCutTorComparison a (G.incidenceParameterCoordinateIdeal r)
    (G.incidenceParameterCoordinateIdeal s) (G.incidenceParameterCoordinateIdeal_origin r)
    (G.incidenceParameterCoordinateIdeal_origin s) ha p

/-- Pencil, Artin and all intermediate sections have compatible actual Tor products. -/
theorem incidenceSectionTorComparison_mul (r s p q : ℕ)
    (x : G.incidenceSectionTor a r p) (y : G.incidenceSectionTor a r q) :
    G.incidenceSectionTorComparison a ha r s (p+q) (G.incidenceSectionTorProduct a ha r p q x y) =
      G.incidenceSectionTorProduct a ha s p q
        (G.incidenceSectionTorComparison a ha r s p x)
        (G.incidenceSectionTorComparison a ha r s q y) :=
  G.incidenceCutTorComparison_mul a (G.incidenceParameterCoordinateIdeal r)
    (G.incidenceParameterCoordinateIdeal s) (G.incidenceParameterCoordinateIdeal_origin r)
    (G.incidenceParameterCoordinateIdeal_origin s) ha p q x y

/-- Successive-section comparisons preserve the natural internal components. -/
theorem incidenceSectionTorComparison_internal (r s p q : ℕ)
    (x : G.incidenceSectionTor a r p) :
    G.incidenceSectionTorComparison a ha r s p x ∈ G.incidenceSectionTorInternalPiece a ha s p q ↔
      x ∈ G.incidenceSectionTorInternalPiece a ha r p q :=
  G.incidenceCutTorComparison_internal a (G.incidenceParameterCoordinateIdeal r)
    (G.incidenceParameterCoordinateIdeal s) (G.incidenceParameterCoordinateIdeal_origin r)
    (G.incidenceParameterCoordinateIdeal_origin s) ha p q x

end BPFixedPoints.Multigraph
