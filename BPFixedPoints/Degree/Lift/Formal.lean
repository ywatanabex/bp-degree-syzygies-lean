import BPFixedPoints.Degree.Lift.LimitSystem

/-!
# Unique lifting of weak-coupling limit points

For c_e≠0, β_i≠0,−1 over algebraically closed characteristic-zero K, each
limit point of the auxiliary system s_e=1+t c_e has a unique lift to K⟦t⟧,
by Hensel and invertibility of the limit Jacobian. The limit points, specified
by an active set S and vertex roots F, number Q(G). The lifts are distinct
and satisfy A_α≠0,−1 and F_i≠0,−1 in K⟦t⟧.
This is the formal-power-series version of the analytic ε→0 statement.
Convergence and the complex analytic implicit function theorem are not treated.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP MvPolynomial
open scoped PowerSeries

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)
variable {K : Type*} [Field K] [DecidableEq K]

/-- Q(G)≥1, from the empty-support term. -/
theorem Q_pos : 0 < G.Q := by
  unfold Q QOn
  have h1 : G.wt phi ∅ = 1 := by simp [wt]
  have := Finset.single_le_sum (f := fun S => G.wt phi S) (fun S _ => Nat.zero_le _)
    (Finset.empty_mem_powerset (Finset.univ : Finset E))
  simp only [h1] at this
  omega

/-- The residue Jacobian of the family is the limit-system Jacobian. -/
theorem jacRes_weakSystem (c : E → K) (β : V → K) (x₀ : Var V E → K) :
    jacRes (G.weakSystem c β) x₀ = G.jacLimit c β x₀ := by
  ext i j
  simp only [jacRes, jacLimit, Matrix.of_apply]
  rw [map_eval', ← pderiv_map, map_constantCoeff_weakSystem]
  congr 1

/-- The residue Jacobian determinant at a limit point is nonzero. -/
theorem det_jacRes_weakSystem_ne_zero [CharZero K] {c : E → K} {β : V → K} (hβ1 : ∀ i, β i ≠ -1)
    {S : Finset E} {F : V → K} (hF : ∀ i, VertexLimitEq (G.deg S i) (β i) (F i)) :
    (jacRes (G.weakSystem c β) (G.limitPoint S F)).det ≠ 0 := by
  rw [jacRes_weakSystem]
  have hinj : Function.Injective (G.jacLimit c β (G.limitPoint S F)).mulVec := by
    intro v w hvw
    have h0 : (G.jacLimit c β (G.limitPoint S F)).mulVec (v - w) = 0 := by
      rw [Matrix.mulVec_sub, hvw, sub_self]
    exact sub_eq_zero.1 (G.jacLimit_mulVec_eq_zero hβ1 hF (v - w) h0)
  have hu := Matrix.mulVec_injective_iff_isUnit.1 hinj
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  exact hu.ne_zero

/-- A limit point is a zero of the residue family. -/
theorem constantCoeff_eval_weakSystem_limitPoint (c : E → K) {β : V → K} (hβ1 : ∀ i, β i ≠ -1)
    {S : Finset E} {F : V → K} (hF : ∀ i, VertexLimitEq (G.deg S i) (β i) (F i)) (v : Var V E) :
    PowerSeries.constantCoeff
      (eval (fun j => PowerSeries.C (G.limitPoint S F j)) (G.weakSystem c β v)) = 0 := by
  rw [map_eval', map_constantCoeff_weakSystem]
  have h : (PowerSeries.constantCoeff ∘ fun j => PowerSeries.C (G.limitPoint S F j)) =
      G.limitPoint S F := by
    funext j; simp
  rw [h]
  exact G.eval_limitSystem₀_limitPoint hβ1 hF v

/-- Unique lift of a limit point to K⟦t⟧. -/
theorem exists_unique_lift [CharZero K] (c : E → K) {β : V → K} (hβ1 : ∀ i, β i ≠ -1)
    {S : Finset E} {F : V → K} (hF : ∀ i, VertexLimitEq (G.deg S i) (β i) (F i)) :
    ∃! x : Var V E → K⟦X⟧,
      (∀ j, PowerSeries.constantCoeff (x j) = G.limitPoint S F j) ∧
        ∀ v, eval x (G.weakSystem c β v) = 0 :=
  hensel_lift (G.weakSystem c β) (G.limitPoint S F)
    (G.constantCoeff_eval_weakSystem_limitPoint c hβ1 hF)
    (G.det_jacRes_weakSystem_ne_zero hβ1 hF)

/-- Admissibility of the lifted root: A_α,F_i≠0,-1 in K[[t]]. -/
theorem lift_admissible {c : E → K} (hc : ∀ e, c e ≠ 0) {β : V → K} (hβ1 : ∀ i, β i ≠ -1)
    {S : Finset E} {F : V → K} (hF : ∀ i, VertexLimitEq (G.deg S i) (β i) (F i))
    (x : Var V E → K⟦X⟧) (hx0 : ∀ j, PowerSeries.constantCoeff (x j) = G.limitPoint S F j)
    (hx : ∀ v, eval x (G.weakSystem c β v) = 0) :
    (∀ α, x (Sum.inl α) ≠ 0) ∧ (∀ α, x (Sum.inl α) + 1 ≠ 0) ∧
      (∀ i, x (Sum.inr i) ≠ 0) ∧ (∀ i, x (Sum.inr i) + 1 ≠ 0) := by
  have hL := G.isLimitSolution_limitCoords hβ1 hF
  have hA0 : ∀ α, x (Sum.inl α) ≠ 0 := by
    intro α h0
    have h := hx0 (Sum.inl α)
    rw [h0, map_zero] at h
    simp only [limitPoint, limitCoords] at h
    split_ifs at h with hα
    · exact absurd h (by norm_num)
    · exact hL.ne_zero _ h.symm
  have hF0 : ∀ i, x (Sum.inr i) ≠ 0 := by
    intro i h0
    have h := hx0 (Sum.inr i)
    rw [h0, map_zero] at h
    exact hL.ne_zero i h.symm
  have hF1 : ∀ i, x (Sum.inr i) + 1 ≠ 0 := by
    intro i h0
    have h := hx0 (Sum.inr i)
    have h1 : x (Sum.inr i) = -1 := by linear_combination h0
    rw [h1, map_neg, map_one] at h
    exact hL.ne_neg_one i h.symm
  refine ⟨hA0, ?_, hF0, hF1⟩
  intro α h0
  have h := hx (Sum.inl (rev α))
  simp only [weakSystem, edgePoly, eval_add, eval_mul, eval_sub, eval_X, eval_C, map_one,
    rev_rev, rev_fst] at h
  rw [h0, mul_zero, zero_add] at h
  have hX : (PowerSeries.X : K⟦X⟧) ≠ 0 := PowerSeries.X_ne_zero
  have hC : (PowerSeries.C (c α.1) : K⟦X⟧) ≠ 0 := by
    intro hc0
    have := congrArg PowerSeries.constantCoeff hc0
    rw [PowerSeries.constantCoeff_C, map_zero] at this
    exact hc α.1 this
  rcases mul_eq_zero.1 h with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · rcases mul_eq_zero.1 h2 with h3 | h3
      · exact hX h3
      · exact hC h3
    · exact hA0 _ h2
  · exact hA0 _ h1

section Lifts

variable [CharZero K] (c : E → K) (β : V → K) (hβ1 : ∀ i, β i ≠ -1)

/-- Lift of a limit point p=(S,F), chosen from the unique Hensel root. -/
noncomputable def liftOf (p : G.LimitParams β) : Var V E → K⟦X⟧ :=
  Classical.choose (G.exists_unique_lift c hβ1 (S := p.1.1) (F := p.1.2) p.2).exists

theorem liftOf_spec (p : G.LimitParams β) :
    (∀ j, PowerSeries.constantCoeff (G.liftOf c β hβ1 p j) = G.limitPoint p.1.1 p.1.2 j) ∧
      ∀ v, eval (G.liftOf c β hβ1 p) (G.weakSystem c β v) = 0 :=
  Classical.choose_spec (G.exists_unique_lift c hβ1 (S := p.1.1) (F := p.1.2) p.2).exists

include hβ1 in
/-- The coordinate map on limit points is injective: F is recovered from inr coordinates and S from the active support. -/
theorem limitPoint_injective_on {S S' : Finset E} {F F' : V → K}
    (hF : ∀ i, VertexLimitEq (G.deg S i) (β i) (F i))
    (hF' : ∀ i, VertexLimitEq (G.deg S' i) (β i) (F' i))
    (h : G.limitPoint S F = G.limitPoint S' F') : S = S' ∧ F = F' := by
  have hFF : F = F' := by
    funext i
    exact congrFun h (Sum.inr i)
  subst hFF
  refine ⟨?_, rfl⟩
  have hA : G.limitCoords S F = G.limitCoords S' F := by
    funext α
    exact congrFun h (Sum.inl α)
  rw [← activeSet_limitCoords hβ1 hF, ← activeSet_limitCoords hβ1 hF', hA]

theorem liftOf_injective : Function.Injective (G.liftOf c β hβ1) := by
  intro p q hpq
  have hp := (G.liftOf_spec c β hβ1 p).1
  have hq := (G.liftOf_spec c β hβ1 q).1
  have h : G.limitPoint p.1.1 p.1.2 = G.limitPoint q.1.1 q.1.2 := by
    funext j
    rw [← hp j, ← hq j, hpq]
  obtain ⟨hS, hF⟩ := G.limitPoint_injective_on β hβ1 p.2 q.2 h
  apply Subtype.ext
  exact Prod.ext hS hF

end Lifts

/-- **Formal version.** For algebraically closed characteristic-zero K, c_e≠0 and β_i≠0,−1, the system s_e=1+t c_e has Q(G) distinct K⟦t⟧-solutions satisfying A_α≠0,−1 and F_i≠0,−1. -/
theorem exists_Q_formal_solutions [IsAlgClosed K] [CharZero K] (c : E → K) (hc : ∀ e, c e ≠ 0)
    (β : V → K) (hβ0 : ∀ i, β i ≠ 0) (hβ1 : ∀ i, β i ≠ -1) :
    ∃ sols : Finset (Var V E → K⟦X⟧), sols.card = G.Q ∧ ∀ x ∈ sols,
      (∀ v, eval x (G.weakSystem c β v) = 0) ∧
      (∀ α, x (Sum.inl α) ≠ 0) ∧ (∀ α, x (Sum.inl α) + 1 ≠ 0) ∧
      (∀ i, x (Sum.inr i) ≠ 0) ∧ (∀ i, x (Sum.inr i) + 1 ≠ 0) := by
  classical
  have hcard : Nat.card (G.LimitParams β) = G.Q := by
    rw [← Nat.card_congr (G.limitSolutionsEquiv β hβ1), G.card_limitSolutions β hβ0 hβ1]
  have hfin : Finite (G.LimitParams β) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact G.Q_pos.ne')
  let _ := Fintype.ofFinite (G.LimitParams β)
  refine ⟨Finset.univ.image (G.liftOf c β hβ1), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (G.liftOf_injective c β hβ1), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hcard]
  · intro x hx
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨h0, hsol⟩ := G.liftOf_spec c β hβ1 p
    exact ⟨hsol, G.lift_admissible hc hβ1 p.2 _ h0 hsol⟩

end Multigraph

end BPFixedPoints
