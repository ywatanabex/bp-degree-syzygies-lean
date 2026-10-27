import BPFixedPoints.Incidence.IncidenceParameterCutTor
import BPFixedPoints.Incidence.IncidenceParameterSections

/-! # Tor of the successive linear sections, including pencil and Artin cuts -/

namespace BPFixedPoints.Multigraph

open MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The first r coordinate parameters, in the parameter polynomial ring. -/
noncomputable def incidenceParameterCoordinateIdeal (r : ℕ) : Ideal (MvPolynomial (Fin G.dG) ℂ) :=
  Ideal.ofList ((List.ofFn (X : Fin G.dG → MvPolynomial (Fin G.dG) ℂ)).take r)

theorem incidenceParameterCoordinateIdeal_origin (r : ℕ) :
    G.incidenceParameterCoordinateIdeal r ≤ RingHom.ker constantCoeff := by
  apply Ideal.span_le.mpr
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hx)
  exact constantCoeff_X ℂ i

/-- These parameter relations are exactly the previously defined successive incidence cuts. -/
theorem incidenceParameterCoordinateIdeal_image (a : G.IncidenceLinearParameters) (r : ℕ) :
    (G.incidenceParameterCoordinateIdeal r).map (G.incidenceParameterHom a).toRingHom =
      G.incidenceParameterSectionIdeal a r := by
  unfold incidenceParameterCoordinateIdeal incidenceParameterSectionIdeal
  rw [Ideal.map_ofList, List.map_take, List.map_ofFn]
  apply congrArg Ideal.ofList
  apply congrArg (List.take r)
  apply congrArg List.ofFn
  funext i
  exact G.incidenceParameterHom_X a i

/-- Actual Tor for the first r linear cuts, over the correspondingly cut coefficient ring. -/
noncomputable def incidenceSectionTor (a : G.IncidenceLinearParameters) (r p : ℕ) :=
  G.incidenceParameterCutTor a (G.incidenceParameterCoordinateIdeal r)
    (G.incidenceParameterCoordinateIdeal_origin r) p

noncomputable def incidenceSectionTorEquiv (a : G.IncidenceLinearParameters)
    (ha : a ∈ G.incidenceFiniteParameterLocus) (r p : ℕ) :
    G.incidenceSectionTor a r p ≃ₗ[ℂ] G.incidenceTor p :=
  G.incidenceParameterCutTorEquiv a (G.incidenceParameterCoordinateIdeal r)
    (G.incidenceParameterCoordinateIdeal_origin r) ha p

theorem finrank_incidenceSectionTor (a : G.IncidenceLinearParameters)
    (ha : a ∈ G.incidenceFiniteParameterLocus) (r p : ℕ) :
    Module.finrank ℂ (G.incidenceSectionTor a r p) =
      ∑ q ∈ Finset.range (Fintype.card E + 1), G.betti p q :=
  (G.incidenceSectionTorEquiv a ha r p).finrank_eq.trans (G.finrank_incidenceTor p)

/-- Every successive section has the same total Tor dimension, in particular r=dG-1 and r=dG. -/
theorem sum_finrank_incidenceSectionTor (a : G.IncidenceLinearParameters)
    (ha : a ∈ G.incidenceFiniteParameterLocus) (r : ℕ) :
    ∑ p ∈ Finset.range (Fintype.card E + 1),
      Module.finrank ℂ (G.incidenceSectionTor a r p) = G.Q :=
  G.sum_finrank_incidenceParameterCutTor a (G.incidenceParameterCoordinateIdeal r)
    (G.incidenceParameterCoordinateIdeal_origin r) ha

end BPFixedPoints.Multigraph
