import BPFixedPoints.Family.FiniteCover
import BPFixedPoints.Family.DimensionTools

/-!
# Krull dimension of the total admissible BP space

The open set of free belief coordinates (u_v,q_e) has dimension n+m.
The belief ring is an injective integral extension, hence has the same dimension.
Transfer back to `FamilyRing` by the actual ring isomorphism, without assuming
irreducibility.
-/

namespace BPFixedPoints.Multigraph

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : Multigraph V E)

theorem ringKrullDim_beliefBaseRing :
    ringKrullDim G.BeliefBaseRing =
      ((Fintype.card E + Fintype.card V : ℕ) : WithBot ℕ∞) := by
  simpa [Nat.card_eq_fintype_card, Fintype.card_sum, Nat.add_comm] using
    ringKrullDim_away_mvPolynomial G.beliefBaseDen_ne_zero

theorem ringKrullDim_beliefRing :
    ringKrullDim G.BeliefRing =
      ((Fintype.card E + Fintype.card V : ℕ) : WithBot ℕ∞) := by
  letI := G.beliefRing_integral
  have hinj : Function.Injective (algebraMap G.BeliefBaseRing G.BeliefRing) :=
    G.beliefBaseHom_injective
  exact (ringKrullDim_eq_of_integral_injective hinj).trans G.ringKrullDim_beliefBaseRing

/-- The original admissible BP coordinate ring has dimension m+n. -/
theorem familyRing_krullDim :
    ringKrullDim G.FamilyRing =
      ((Fintype.card E + Fintype.card V : ℕ) : WithBot ℕ∞) :=
  G.familyRingEquivBeliefRing.toRingEquiv.ringKrullDim.trans G.ringKrullDim_beliefRing

end BPFixedPoints.Multigraph
