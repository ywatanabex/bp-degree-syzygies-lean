import BPFixedPoints.Incidence.IncidenceMaximalDepth
import BPFixedPoints.Incidence.RegularArtinQuotient

/-!
# Regular Artin quotients of the original incidence ring

Quotient the actual ring by a regular sequence of length d_G. This file's
existence theorem does not include selection of generic linear forms or the
graded Hilbert series of the quotient.
-/

namespace BPFixedPoints.Multigraph

open ResolutionTools RingTheory.Sequence
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance incArtinAlgebra : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra
noncomputable local instance incArtinFinite : Module.Finite (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom_finite
local instance incArtinNoetherian : IsNoetherianRing G.IncidenceRing :=
  IsNoetherianRing.of_finite (IncCoeffRing E) G.IncidenceRing
local instance incArtinTower : IsScalarTower ℂ (IncCoeffRing E) G.IncidenceRing :=
  IsScalarTower.of_algHom G.coeffHom
local instance incArtinFiniteType : Algebra.FiniteType ℂ G.IncidenceRing :=
  Algebra.FiniteType.trans (R := ℂ) (S := IncCoeffRing E) (A := G.IncidenceRing)
    inferInstance inferInstance

/-- A quotient by any maximal-length ring-regular sequence is Artinian and finite-dimensional over ℂ. -/
theorem incidence_regular_quotient_artinian (rs : List G.IncidenceRing)
    (hlen : rs.length = G.dG) (hreg : IsRegular G.IncidenceRing rs) :
    IsArtinianRing (G.IncidenceRing ⧸ Ideal.ofList rs) ∧
      Module.Finite ℂ (G.IncidenceRing ⧸ Ideal.ofList rs) := by
  have hd : ringKrullDim G.IncidenceRing = (rs.length : WithBot ℕ∞) := by
    rw [hlen, G.incidenceRing_krullDim]
  exact ⟨isArtinian_quotient_of_regular_length_dim rs hreg hd,
    finite_quotient_of_regular_length_dim ℂ rs hreg hd⟩

/-- Every maximal ideal contains a length-d_G regular sequence giving a nonzero finite-dimensional Artin quotient. -/
theorem exists_incidence_regular_artin_quotient
    (P : Ideal G.IncidenceRing) [P.IsMaximal] :
    ∃ rs : List G.IncidenceRing, rs.length = G.dG ∧ (∀ r ∈ rs, r ∈ P) ∧
      IsRegular G.IncidenceRing rs ∧ Ideal.ofList rs ≠ ⊤ ∧
      IsArtinianRing (G.IncidenceRing ⧸ Ideal.ofList rs) ∧
      Module.Finite ℂ (G.IncidenceRing ⧸ Ideal.ofList rs) := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := G.exists_incidence_ring_regular_sequence_in_maximal P
  refine ⟨rs, hlen, hmem, hreg, ?_, G.incidence_regular_quotient_artinian rs hlen hreg⟩
  intro h
  have hle : Ideal.ofList rs ≤ P := Ideal.span_le.mpr hmem
  rw [h] at hle
  exact (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal)) (top_unique hle)

end BPFixedPoints.Multigraph
