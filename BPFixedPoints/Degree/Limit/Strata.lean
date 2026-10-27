import BPFixedPoints.Degree.Limit.Points

/-!
# Stratification by active sets and 𝒬_G(x,z)

A weak-coupling limit solution is determined by its active set S, where A_α=−1,
and its vertex roots (`limitSolutionsEquiv`). A fixed S gives ∏_i φ(d_S(i))
points (`card_limitSolutions_activeSet`). Their generating function by
(|S|,v(S)), where v(S) counts vertices touched by S, is 𝒬_G(x,z)
(`Qpoly2_eq_sum_strata`).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)
variable {K : Type*} [Field K] [DecidableEq K]

/-- Limit points with active edge set S. -/
def LimitStratum (β : V → K) (S : Finset E) : Type _ :=
  {p : G.LimitSolutions β // activeSet p.1.1 = S}

/-- The stratum S corresponds to the tuple of vertex roots. -/
def limitStratumEquiv (β : V → K) (hβ1 : ∀ i, β i ≠ -1) (S : Finset E) :
    G.LimitStratum β S ≃ {F : V → K // ∀ i, VertexLimitEq (G.deg S i) (β i) (F i)} where
  toFun p := ⟨p.1.1.2, fun i => by
    have := p.1.2.vertexLimitEq i
    rwa [p.2] at this⟩
  invFun F := ⟨⟨(G.limitCoords S F.1, F.1), G.isLimitSolution_limitCoords hβ1 F.2⟩,
    activeSet_limitCoords hβ1 F.2⟩
  left_inv p := by
    obtain ⟨⟨⟨A, F⟩, h⟩, hS⟩ := p
    apply Subtype.ext
    apply Subtype.ext
    simp only at hS ⊢
    rw [← hS, ← h.eq_limitCoords]
  right_inv F := rfl

/-- The stratum with active support S has exactly product_i φ(d_S(i)) points. -/
theorem card_limitSolutions_activeSet [IsAlgClosed K] [CharZero K] (β : V → K)
    (hβ0 : ∀ i, β i ≠ 0) (hβ1 : ∀ i, β i ≠ -1) (S : Finset E) :
    Nat.card (G.LimitStratum β S) = G.wt phi S := by
  rw [Nat.card_congr (G.limitStratumEquiv β hβ1 S),
    Nat.card_congr (Equiv.subtypePiEquivPi
      (p := fun i (x : K) => VertexLimitEq (G.deg S i) (β i) x))]
  have : ∀ i : V, Finite {x : K // VertexLimitEq (G.deg S i) (β i) x} :=
    fun i => finite_vertexLimitEq K _ _ (hβ0 i) (hβ1 i)
  rw [Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => card_vertexLimitEq K _ _ (hβ0 i) (hβ1 i)

/-- The generating function of limit points by active-set size |S| and support size v(S) is 𝒬_G(x,z). -/
theorem Qpoly2_eq_sum_strata [IsAlgClosed K] [CharZero K] (β : V → K)
    (hβ0 : ∀ i, β i ≠ 0) (hβ1 : ∀ i, β i ≠ -1) :
    G.Qpoly2 = ∑ S : Finset E, MvPolynomial.X 0 ^ S.card * MvPolynomial.X 1 ^ (G.support S).card *
      ((Nat.card (G.LimitStratum β S) : ℕ) : MvPolynomial (Fin 2) ℤ) := by
  rw [Qpoly2, Qpoly2On, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [G.card_limitSolutions_activeSet β hβ0 hβ1 S]

end Multigraph

end BPFixedPoints
