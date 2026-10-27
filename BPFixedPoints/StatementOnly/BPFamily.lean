import BPFixedPoints.Degree.GenericDegree
import BPFixedPoints.Family.Smooth
import BPFixedPoints.Family.Domain
import BPFixedPoints.Family.Dimension

/-!
# Geometric content of `prop:bp-family`

The paper states that the admissible total space
𝒳_G={f_α=0,D≠0}⊂P_G×𝔸^{2m}, P_G=(ℂ*)^{m+n}, is smooth, irreducible and
of dimension m+n, and its projection is dominant, generically finite, finite
étale of degree N(G) on a nonempty Zariski open set.

The finite simple fiber count is `HasGenericDegree` in `Degree/GenericDegree.lean`,
with N=Q for loopless G (`hasGenericDegree_Q`). Smoothness is `familyRing_smooth`
in `Family/Smooth.lean`, using normalized beliefs, BP reconstruction and
simple quadratic lifts through square-zero extensions.
This file proves that the original ring
A_G=ℂ[a,b,y][1/(∏a·∏b·D)]/(f_α) (`FamilyRing`) is a domain, hence reduced
and irreducible, of Krull dimension m+n. An actual belief-ring isomorphism,
an embedding into edgewise double covers and an injective integral extension
of a free-belief localization give the proof. The degree of the finite étale
2^m cover is not formalized.
Definitions are in `Family/Ring.lean`; parameters are polynomial variables,
unlike the field-valued functions in `Degree/Equations.lean`.
-/

namespace BPFixedPoints.Multigraph

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

/-- **Irreducibility in `prop:bp-family`.** 𝒳_G is irreducible and reduced: its coordinate ring is a domain. -/
theorem familyRing_isDomain (hG : G.Loopless) : IsDomain G.FamilyRing := by
  exact G.familyRing_domain

/-- **Dimension in `prop:bp-family`.** dim 𝒳_G=m+n. -/
theorem ringKrullDim_familyRing (hG : G.Loopless) :
    ringKrullDim G.FamilyRing = ((Fintype.card E + Fintype.card V : ℕ) : WithBot ℕ∞) := by
  exact G.familyRing_krullDim

end BPFixedPoints.Multigraph

