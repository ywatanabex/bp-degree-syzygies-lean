import BPFixedPoints.Degree.Equations

/-!
# Edge normalization, local consistency and propagation of F_i=−1

For dart α on e={i,j}, set X=X_α and Y=X_ᾱ. Unnormalized edge weights for
(+,+),(+,−),(−,+),(−,−) are (aXY,X,Y,a). At a fixed point the marginal ratio
(aXY+X)/(Y+a)=F_i (`edge_marginal_eq`), using y_ᾱ(Y+a)=aY+1 and F_i=Xy_ᾱ.
Thus the marginal is proportional to the vertex belief (F_i:1).
The normalizer is Z_e=aXY+X+Y+a=(1+F_i)(Y+a) (`normalization_identity`),
nonzero when the update denominator and 1+F_i are nonzero (`edgeNormalizer_ne_zero`).
Symmetry gives (1+F_i)(Y+a)=(1+F_j)(X+a). With nonzero update denominators,
1+F_i=0 iff 1+F_j=0 (`one_add_totalField_tail_eq_zero_iff`); connectedness
propagates this to all vertices (`one_add_totalField_eq_zero_of_connected`).
This last statement precedes imposing the normalization condition 1+F≠0.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)
variable {K : Type*} [Field K] (a : E → K) (b : V → K) (y : Dart E → K)

/-- **Local consistency.** At a fixed point the positive marginal aXY+X equals F_i times the negative marginal Y+a. -/
theorem edge_marginal_eq (hfix : G.IsFixedPoint a b y) (α : Dart E) :
    a α.1 * G.cavity b y α * G.cavity b y (rev α) + G.cavity b y α =
      G.totalField b y (G.tail α) * (G.cavity b y (rev α) + a α.1) := by
  rw [G.totalField_tail_eq b y α]
  have h := hfix (rev α)
  unfold bpPoly at h
  rw [rev_fst] at h
  linear_combination -(G.cavity b y α) * h

/-- Edge normalizer Z_e=aXY+X+Y+a. -/
def edgeNormalizer (α : Dart E) : K :=
  a α.1 * G.cavity b y α * G.cavity b y (rev α) + G.cavity b y α + G.cavity b y (rev α) + a α.1

/-- **Normalization.** At a fixed point, nonzero update denominator and 1+F_i≠0 imply Z_e≠0. -/
theorem edgeNormalizer_ne_zero (hfix : G.IsFixedPoint a b y)
    (hden : ∀ α, G.cavity b y α + a α.1 ≠ 0) (hF : ∀ i, 1 + G.totalField b y i ≠ 0)
    (α : Dart E) : G.edgeNormalizer a b y α ≠ 0 := by
  rw [edgeNormalizer, ← G.normalization_identity a b y hfix α]
  have := hden (rev α)
  rw [rev_fst] at this
  exact mul_ne_zero (hF _) this

/-- Z_e is independent of orientation. -/
theorem edgeNormalizer_rev (α : Dart E) :
    G.edgeNormalizer a b y (rev α) = G.edgeNormalizer a b y α := by
  simp only [edgeNormalizer, rev_rev, rev_fst]
  ring

/-- **One edge.** At a fixed point with nonzero update denominators, 1+F_{t(α)}=0 iff 1+F_{h(α)}=0. -/
theorem one_add_totalField_tail_eq_zero_iff (hfix : G.IsFixedPoint a b y)
    (hden : ∀ α, G.cavity b y α + a α.1 ≠ 0) (α : Dart E) :
    1 + G.totalField b y (G.tail α) = 0 ↔ 1 + G.totalField b y (G.head α) = 0 := by
  have h1 := G.normalization_identity a b y hfix α
  have h2 := G.normalization_identity a b y hfix (rev α)
  rw [tail_rev, rev_rev, rev_fst] at h2
  have e : (1 + G.totalField b y (G.tail α)) * (G.cavity b y (rev α) + a α.1) =
      (1 + G.totalField b y (G.head α)) * (G.cavity b y α + a α.1) := by
    rw [h1, h2]; ring
  have hα := hden α
  have hr := hden (rev α)
  rw [rev_fst] at hr
  constructor
  · intro h
    rw [h, zero_mul] at e
    exact (mul_eq_zero.1 e.symm).resolve_right hα
  · intro h
    rw [h, zero_mul] at e
    exact (mul_eq_zero.1 e).resolve_right hr

/-- **Propagation.** On a connected graph, a fixed point with nonzero update denominators and F_i=−1 at one vertex has F_j=−1 at every vertex. -/
theorem one_add_totalField_eq_zero_of_connected (hc : G.Connected) (hfix : G.IsFixedPoint a b y)
    (hden : ∀ α, G.cavity b y α + a α.1 ≠ 0) {i : V} (hi : 1 + G.totalField b y i = 0) (j : V) :
    1 + G.totalField b y j = 0 := by
  have hpath := hc.2.2 i (Finset.mem_univ _) j (Finset.mem_univ _)
  induction hpath with
  | refl => exact hi
  | @tail c d _ hcd ih =>
    obtain ⟨e, -, he⟩ := hcd
    have key := G.one_add_totalField_tail_eq_zero_iff a b y hfix hden (e, true)
    simp only [tail, head, Bool.cond_true] at key
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2] at key; exact key.1 ih
    · rw [h1, h2] at key; exact key.2 ih

end Multigraph

end BPFixedPoints
