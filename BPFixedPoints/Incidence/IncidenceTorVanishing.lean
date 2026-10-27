import BPFixedPoints.Incidence.ResolutionTorGrading

/-!
# Vanishing of the internal Tor pieces below the homological degree

The isomorphism `incidenceTorExteriorEquiv` of the internal-degree-q piece of `Tor_p` with
`H^{q-p}` of the q-th exterior bundle is stated for `p ≤ q`, where `q - p` is the cohomological
degree. This file records the complementary clause: for `q < p` the internal piece is zero
(`incidenceTorInternalPiece_eq_bot_of_lt`), so no negative cohomological degree is needed. A
basis element of homological degree `p` has internal degree `|S| ≥ |S| - v(S) = p`. The Betti
number `β_{p,q}` vanishes accordingly (`betti_eq_zero_of_lt`).
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The homological degree of a resolution basis element is at most its internal degree. -/
theorem incResolutionDegree_le_internalDegree (b : G.IncResolutionBasis) :
    G.incResolutionDegree b ≤ G.incResolutionInternalDegree b := by
  unfold incResolutionDegree incResolutionInternalDegree
  omega

/-- Internal-degree components below the homological degree vanish. -/
theorem incidenceTorInternalPiece_eq_bot_of_lt {p q : ℕ} (h : q < p) :
    G.incidenceTorInternalPiece p q = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply (G.incidenceTorEquivState p).injective
  ext b
  have hs := (Finsupp.mem_supported' ℂ _).mp
    ((G.mem_incidenceTorInternalPiece_iff p q x).mp hx)
  have hb := G.incResolutionDegree_le_internalDegree b.val
  have hp := b.property
  simpa using hs b (by change G.incResolutionInternalDegree b.val ≠ q; omega)

/-- The Betti number `β_{p,q}` vanishes for `q < p`. -/
theorem betti_eq_zero_of_lt {p q : ℕ} (h : q < p) : G.betti p q = 0 := by
  rw [← G.finrank_incidenceTorInternalPiece, G.incidenceTorInternalPiece_eq_bot_of_lt h,
    finrank_bot]

end BPFixedPoints.Multigraph
