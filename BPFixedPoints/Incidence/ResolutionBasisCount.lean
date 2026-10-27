import BPFixedPoints.Incidence.ResolutionStates

/-!
# The two degrees of the actual incidence resolution basis

These are the bases used by `incResolutionDifferential`, not a new complex
with the desired ranks imposed as a definition. The internal degree of a
state generator is the number of edges in its state. The theorem below
identifies the cardinality of each actual basis fibre with the previously
defined state-sum table. Compatibility of the differential with this degree
is a separate assertion; a basis count alone is not a graded Tor theorem.
-/

namespace BPFixedPoints.Multigraph

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

/-- The coefficient-ring grading shift of an actual state generator. -/
def incResolutionInternalDegree (b : G.IncResolutionBasis) : ℕ := b.1.card

/-- Actual resolution generators in homological degree `p` and internal degree `q`. -/
abbrev IncBigradedBasis (p q : ℕ) :=
  {b : G.IncResolutionBasis //
    G.incResolutionDegree b = p ∧ G.incResolutionInternalDegree b = q}

/-- The bigraded basis count is the state-sum table, without a rank hypothesis. -/
theorem card_incBigradedBasis (p q : ℕ) :
    Fintype.card (G.IncBigradedBasis p q) = G.betti p q := by
  classical
  change Fintype.card {b : G.IncResolutionBasis //
    G.incResolutionDegree b = p ∧ G.incResolutionInternalDegree b = q} = _
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ b : G.IncResolutionBasis,
    if G.incResolutionDegree b = p ∧ G.incResolutionInternalDegree b = q
    then (1 : ℕ) else 0) = _
  rw [Fintype.sum_sigma]
  unfold betti
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hp : S.card - (G.support S).card = p <;>
    by_cases hq : S.card = q <;>
    simp [incResolutionDegree, incResolutionInternalDegree, hp, hq,
      wt, Fintype.card_pi]

/-- The full actual basis has `Q(G)` elements. -/
theorem card_incResolutionBasis : Fintype.card G.IncResolutionBasis = G.Q := by
  classical
  rw [Fintype.card_sigma, Q, QOn, Finset.powerset_univ]
  simp only [Fintype.card_pi, Fintype.card_fin, wt]

/-- The internal shift of an actual generator is at most the number of edges. -/
theorem incResolutionInternalDegree_le (b : G.IncResolutionBasis) :
    G.incResolutionInternalDegree b ≤ Fintype.card E := Finset.card_le_univ b.1

/-- The two degrees of an actual generator recover its support size. -/
theorem incResolutionDegree_add_support (b : G.IncResolutionBasis) :
    G.incResolutionDegree b + (G.support b.1).card =
      G.incResolutionInternalDegree b := by
  exact Nat.sub_add_cancel (G.incResolutionBasis_card_support_le b)

end BPFixedPoints.Multigraph
