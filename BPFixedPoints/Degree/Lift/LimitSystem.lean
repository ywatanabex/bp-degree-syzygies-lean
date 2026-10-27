import BPFixedPoints.Degree.Lift.Hensel
import BPFixedPoints.Degree.Limit.Points

/-!
# One-parameter weak coupling and its limit at t=0

Write s_e=1+t c_e with constant β_i over K⟦t⟧, using variables Dart E⊕V
for A_α and F_i respectively. Edge equations are
E_α=(A_α−F_i)(A_ᾱ+1)+t c_e A_α A_ᾱ (20), i=t(α).
Vertex equations are V_i=F_i∏_{α∈in(i)}A_ᾱ−β_i F_i^{d_i}, the denominator-cleared
form of (5), equivalent when F_i≠0.
At t=0, `limitSystem₀` has edge equations (A_α−F_i)(A_ᾱ+1) (16) and the
same vertex equations. Its solutions with F_i≠0 are `IsLimitSolution`.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP MvPolynomial
open scoped PowerSeries

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)
variable {K : Type*} [Field K] [DecidableEq K]

/-- Variable indices: darts for A and vertices for F. -/
abbrev Var (V E : Type*) := Dart E ⊕ V

/-- Edge polynomial (A_α-F_tailα)(A_revα+1)+ε c_e A_α A_revα over R. -/
noncomputable def edgePoly {R : Type*} [CommRing R] (ε : R) (c : E → R) (α : Dart E) :
    MvPolynomial (Var V E) R :=
  (X (Sum.inl α) - X (Sum.inr (G.tail α))) * (X (Sum.inl (rev α)) + 1) +
    C (ε * c α.1) * X (Sum.inl α) * X (Sum.inl (rev α))

/-- Vertex polynomial F_i product_{α in in(i)} A_revα-β_i F_i^{d_i}. -/
noncomputable def vertexPoly {R : Type*} [CommRing R] (β : V → R) (i : V) :
    MvPolynomial (Var V E) R :=
  X (Sum.inr i) * ∏ α ∈ G.inDarts i, X (Sum.inl (rev α)) - C (β i) * X (Sum.inr i) ^ G.degree i

/-- One-parameter system over K[[t]], with ε=t. -/
noncomputable def weakSystem (c : E → K) (β : V → K) : Var V E → MvPolynomial (Var V E) K⟦X⟧
  | Sum.inl α => G.edgePoly PowerSeries.X (fun e => PowerSeries.C (c e)) α
  | Sum.inr i => G.vertexPoly (fun i => PowerSeries.C (β i)) i

/-- Limit system over K, with ε=0. -/
noncomputable def limitSystem₀ (c : E → K) (β : V → K) : Var V E → MvPolynomial (Var V E) K
  | Sum.inl α => G.edgePoly 0 c α
  | Sum.inr i => G.vertexPoly β i

/-- Taking constant coefficients of the one-parameter system gives the limit system. -/
theorem map_constantCoeff_weakSystem (c : E → K) (β : V → K) (v : Var V E) :
    map PowerSeries.constantCoeff (G.weakSystem c β v) = G.limitSystem₀ c β v := by
  rcases v with α | i
  · simp [weakSystem, limitSystem₀, edgePoly, map_mul, map_add, map_sub]
  · simp [weakSystem, limitSystem₀, vertexPoly, map_mul, map_sub, map_prod, map_pow]

/-- Arrange a limit point (S,F) as variable values x₀:Var→K. -/
def limitPoint (S : Finset E) (F : V → K) : Var V E → K
  | Sum.inl α => G.limitCoords S F α
  | Sum.inr i => F i

/-- A limit point is a zero of the limit system. -/
theorem eval_limitSystem₀_limitPoint {c : E → K} {β : V → K} (hβ1 : ∀ i, β i ≠ -1)
    {S : Finset E} {F : V → K} (hF : ∀ i, VertexLimitEq (G.deg S i) (β i) (F i)) (v : Var V E) :
    eval (G.limitPoint S F) (G.limitSystem₀ c β v) = 0 := by
  have h := G.isLimitSolution_limitCoords hβ1 hF
  rcases v with α | i
  · simp only [limitSystem₀, edgePoly, limitPoint, eval_add, eval_mul, eval_sub, eval_X, eval_C,
      map_one, zero_mul, add_zero]
    exact h.edge α
  · simp only [limitSystem₀, vertexPoly, limitPoint, eval_sub, eval_mul, eval_X, eval_prod,
      eval_C, eval_pow]
    have hv := h.vertex i
    have hF0 : F i ≠ 0 := h.ne_zero i
    rw [hv, zpow_sub₀ hF0, zpow_one, zpow_natCast]
    field_simp
    ring

/-! ### Evaluation, ring homomorphisms and product derivatives -/

/-- Ring homomorphisms commute with evaluation: φ(g(x))=(φ g)(φ∘x). -/
theorem map_eval' {R S σ : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (x : σ → R)
    (p : MvPolynomial σ R) : φ (eval x p) = eval (φ ∘ x) (map φ p) := by
  rw [eval_map]
  show φ (eval₂ (RingHom.id R) x p) = _
  rw [eval₂_comp_left, RingHom.comp_id]

/-- Evaluation of a partial derivative of a product of distinct variables (Leibniz rule). -/
theorem eval_pderiv_prod_X {R σ ι : Type*} [CommRing R] [DecidableEq σ] [DecidableEq ι]
    (s : Finset ι) (g : ι → σ) (x : σ → R) (v : σ) :
    eval x (pderiv v (∏ γ ∈ s, X (g γ) : MvPolynomial σ R)) =
      ∑ γ ∈ s.filter (fun γ => g γ = v), ∏ δ ∈ s.erase γ, x (g δ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, pderiv_mul, pderiv_X, map_add, eval_mul, eval_mul, ih,
      Finset.filter_insert]
    have hprod : eval x (∏ γ ∈ s, X (g γ) : MvPolynomial σ R) = ∏ δ ∈ s, x (g δ) := by
      simp [eval_prod]
    rw [hprod, eval_X]
    by_cases hga : g a = v
    · rw [if_pos hga, Finset.sum_insert (by simp [ha]), Finset.erase_insert ha, Pi.single_apply,
        if_pos hga, map_one, one_mul, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro γ hγ
      have hγs : γ ∈ s := (Finset.mem_filter.1 hγ).1
      have hne : γ ≠ a := fun h => ha (h ▸ hγs)
      rw [Finset.erase_insert_of_ne hne.symm, Finset.prod_insert (by simp [ha])]
    · rw [if_neg hga, Pi.single_apply, if_neg hga, map_zero, zero_mul, zero_add,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ hγ
      have hγs : γ ∈ s := (Finset.mem_filter.1 hγ).1
      have hne : γ ≠ a := fun h => ha (h ▸ hγs)
      rw [Finset.erase_insert_of_ne hne.symm, Finset.prod_insert (by simp [ha])]

/-! ### Directional derivatives -/

/-- Directional derivative sum_j ∂_j E_α(x) v_j of an edge equation. -/
theorem edgePoly_dirDeriv {R : Type*} [CommRing R] (ε : R) (c : E → R) (α : Dart E)
    (x v : Var V E → R) :
    ∑ j, eval x (pderiv j (G.edgePoly ε c α)) * v j =
      (v (Sum.inl α) - v (Sum.inr (G.tail α))) * (x (Sum.inl (rev α)) + 1) +
        (x (Sum.inl α) - x (Sum.inr (G.tail α))) * v (Sum.inl (rev α)) +
        ε * c α.1 * (v (Sum.inl α) * x (Sum.inl (rev α)) + x (Sum.inl α) * v (Sum.inl (rev α))) := by
  have hd : ∀ j, eval x (pderiv j (G.edgePoly ε c α)) =
      ((if Sum.inl α = j then 1 else 0) - (if Sum.inr (G.tail α) = j then 1 else 0)) *
          (x (Sum.inl (rev α)) + 1) +
        (x (Sum.inl α) - x (Sum.inr (G.tail α))) * (if Sum.inl (rev α) = j then 1 else 0) +
        ε * c α.1 * ((if Sum.inl α = j then 1 else 0) * x (Sum.inl (rev α)) +
          x (Sum.inl α) * (if Sum.inl (rev α) = j then 1 else 0)) := by
    intro j
    simp only [edgePoly, map_add, map_sub, pderiv_mul, pderiv_X, pderiv_C, Pi.single_apply,
      Derivation.map_one_eq_zero, map_one, map_zero, eval_add, eval_sub, eval_mul, eval_X, eval_C]
    simp only [apply_ite (eval x), map_one, map_zero]
    ring
  simp only [hd, add_mul, sub_mul, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  ring

/-- Directional derivative sum_j ∂_j V_i(x) v_j of a vertex equation. -/
theorem vertexPoly_dirDeriv {R : Type*} [CommRing R] (β : V → R) (i : V) (x v : Var V E → R) :
    ∑ j, eval x (pderiv j (G.vertexPoly β i)) * v j =
      v (Sum.inr i) * (∏ α ∈ G.inDarts i, x (Sum.inl (rev α)) -
          β i * (G.degree i : R) * x (Sum.inr i) ^ (G.degree i - 1)) +
        x (Sum.inr i) * ∑ α ∈ G.inDarts i,
          v (Sum.inl (rev α)) * ∏ δ ∈ (G.inDarts i).erase α, x (Sum.inl (rev δ)) := by
  have hd : ∀ j, eval x (pderiv j (G.vertexPoly β i)) =
      (if Sum.inr i = j then 1 else 0) * (∏ α ∈ G.inDarts i, x (Sum.inl (rev α)) -
          β i * (G.degree i : R) * x (Sum.inr i) ^ (G.degree i - 1)) +
        x (Sum.inr i) * ∑ α ∈ (G.inDarts i).filter (fun α => Sum.inl (rev α) = j),
          ∏ δ ∈ (G.inDarts i).erase α, x (Sum.inl (rev δ)) := by
    intro j
    have hP := eval_pderiv_prod_X (G.inDarts i) (fun α => Sum.inl (rev α)) x j
    simp only [vertexPoly, map_sub, pderiv_mul, pderiv_X, pderiv_C, Derivation.leibniz_pow,
      Pi.single_apply, eval_sub, eval_mul, eval_add, eval_X, eval_C, eval_pow, eval_prod,
      map_nsmul, smul_eq_mul, nsmul_eq_mul, hP, map_zero, map_natCast]
    simp only [apply_ite (eval x), map_one, map_zero]
    ring
  simp only [hd, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  · calc ∑ j, (x (Sum.inr i) * ∑ α ∈ (G.inDarts i).filter (fun α => Sum.inl (rev α) = j),
          ∏ δ ∈ (G.inDarts i).erase α, x (Sum.inl (rev δ))) * v j
        = ∑ j, ∑ α ∈ (G.inDarts i).filter (fun α => Sum.inl (rev α) = j),
            x (Sum.inr i) * (v (Sum.inl (rev α)) *
              ∏ δ ∈ (G.inDarts i).erase α, x (Sum.inl (rev δ))) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro α hα
          rw [(Finset.mem_filter.1 hα).2]
          ring
      _ = ∑ α ∈ G.inDarts i, x (Sum.inr i) * (v (Sum.inl (rev α)) *
            ∏ δ ∈ (G.inDarts i).erase α, x (Sum.inl (rev δ))) :=
          Finset.sum_fiberwise (G.inDarts i) (fun α => Sum.inl (rev α)) _
      _ = _ := by rw [Finset.mul_sum]

/-! ### Invertibility of the Jacobian at limit points -/

/-- Jacobian matrix of the limit system over K. -/
noncomputable def jacLimit (c : E → K) (β : V → K) (x : Var V E → K) :
    Matrix (Var V E) (Var V E) K :=
  Matrix.of fun i j => eval x (pderiv j (G.limitSystem₀ c β i))

theorem jacLimit_mulVec (c : E → K) (β : V → K) (x v : Var V E → K) (w : Var V E) :
    (G.jacLimit c β x).mulVec v w = ∑ j, eval x (pderiv j (G.limitSystem₀ c β w)) * v j := by
  simp [jacLimit, Matrix.mulVec, dotProduct]

/-- Product of `limitCoords` over a subset. -/
theorem prod_limitCoords_subset (S : Finset E) (F : V → K) (i : V) {T : Finset (Dart E)}
    (hT : T ⊆ G.inDarts i) :
    ∏ α ∈ T, G.limitCoords S F (rev α) =
      (-1) ^ (T.filter (fun α => α.1 ∈ S)).card * F i ^ (T.filter (fun α => α.1 ∉ S)).card := by
  have h : ∀ α ∈ T, G.limitCoords S F (rev α) = if α.1 ∈ S then -1 else F i := by
    intro α hα
    have := Finset.mem_filter.1 (hT hα)
    unfold limitCoords
    rw [rev_fst, tail_rev, this.2]
  rw [Finset.prod_congr rfl h, Finset.prod_ite, Finset.prod_const, Finset.prod_const]

/--
The vertex-row expression (-1)^k F^m-β d F^{d-1}+m(-1)^k F^m is nonzero
in characteristic zero when k≠1, d=k+m and β=(-1)^k F^{1-k}.
-/
theorem vertex_bracket_ne_zero [CharZero K] {F β : K} {k m : ℕ} (hF : F ≠ 0) (hk : k ≠ 1)
    (hβ : β = (-1) ^ k * F ^ ((1 : ℤ) - k)) :
    (-1) ^ k * F ^ m - β * ((k + m : ℕ) : K) * F ^ (k + m - 1) + (m : K) * ((-1) ^ k * F ^ m) ≠ 0 := by
  rcases Nat.eq_zero_or_pos (k + m) with hd | hd
  · have hk0 : k = 0 := by omega
    have hm0 : m = 0 := by omega
    subst hk0; subst hm0
    simp
  · have hpow : F ^ ((1 : ℤ) - k) * F ^ (k + m - 1) = F ^ m := by
      rw [← zpow_natCast, ← zpow_add₀ hF, Nat.cast_sub hd]
      push_cast
      rw [show (1 : ℤ) - k + (k + m - 1) = m by ring, zpow_natCast]
    have e : (-1) ^ k * F ^ m - β * ((k + m : ℕ) : K) * F ^ (k + m - 1) +
        (m : K) * ((-1) ^ k * F ^ m) = (-1) ^ k * F ^ m * ((1 : K) - k) := by
      rw [hβ]
      calc (-1) ^ k * F ^ m - (-1) ^ k * F ^ ((1 : ℤ) - k) * ((k + m : ℕ) : K) * F ^ (k + m - 1) +
            (m : K) * ((-1) ^ k * F ^ m)
          = (-1) ^ k * F ^ m - (-1) ^ k * ((k + m : ℕ) : K) * (F ^ ((1 : ℤ) - k) * F ^ (k + m - 1)) +
            (m : K) * ((-1) ^ k * F ^ m) := by ring
        _ = _ := by rw [hpow]; push_cast; ring
    rw [e]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hF)) ?_
    intro h0
    have h1 : (k : K) = 1 := by linear_combination -h0
    exact hk (by exact_mod_cast h1)

/-- The Jacobian at a limit point has trivial kernel in characteristic zero. -/
theorem jacLimit_mulVec_eq_zero [CharZero K] {c : E → K} {β : V → K} (hβ1 : ∀ i, β i ≠ -1)
    {S : Finset E} {F : V → K} (hF : ∀ i, VertexLimitEq (G.deg S i) (β i) (F i))
    (v : Var V E → K) (hv : (G.jacLimit c β (G.limitPoint S F)).mulVec v = 0) : v = 0 := by
  have hL := G.isLimitSolution_limitCoords hβ1 hF
  have hF0 : ∀ i, F i ≠ 0 := hL.ne_zero
  have hF1 : ∀ i, F i ≠ -1 := hL.ne_neg_one
  have hedge : ∀ α : Dart E,
      (v (Sum.inl α) - v (Sum.inr (G.tail α))) * (G.limitCoords S F (rev α) + 1) +
        (G.limitCoords S F α - F (G.tail α)) * v (Sum.inl (rev α)) = 0 := by
    intro α
    have h := congrFun hv (Sum.inl α)
    rw [jacLimit_mulVec, Pi.zero_apply] at h
    simp only [limitSystem₀] at h
    rw [G.edgePoly_dirDeriv] at h
    simpa [limitPoint] using h
  have hactive : ∀ α : Dart E, α.1 ∈ S → v (Sum.inl α) = 0 := by
    intro α hα
    have h := hedge (rev α)
    rw [rev_rev, tail_rev] at h
    simp only [limitCoords, rev_fst, hα, ite_true] at h
    have hne : (-1 : K) - F (G.head α) ≠ 0 := fun h0 => hF1 _ (by linear_combination -h0)
    have h2 : (-1 - F (G.head α)) * v (Sum.inl α) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h2 with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hinactive : ∀ α : Dart E, α.1 ∉ S → v (Sum.inl α) = v (Sum.inr (G.tail α)) := by
    intro α hα
    have h := hedge α
    simp only [limitCoords, rev_fst, hα, ite_false, tail_rev, sub_self, zero_mul, add_zero] at h
    have hne : F (G.head α) + 1 ≠ 0 := fun h0 => hF1 _ (by linear_combination h0)
    rcases mul_eq_zero.1 h with h1 | h1
    · linear_combination h1
    · exact absurd h1 hne
  have hvert : ∀ i, v (Sum.inr i) = 0 := by
    intro i
    have h := congrFun hv (Sum.inr i)
    rw [jacLimit_mulVec, Pi.zero_apply] at h
    simp only [limitSystem₀] at h
    rw [G.vertexPoly_dirDeriv] at h
    simp only [limitPoint] at h
    have hkd : G.activeDeg S i ≤ G.degree i := by
      rw [activeDeg, degree]; exact Finset.card_filter_le _ _
    have hcard : ((G.inDarts i).filter (fun α => α.1 ∉ S)).card = G.degree i - G.activeDeg S i := by
      have := Finset.card_filter_add_card_filter_not (s := G.inDarts i) (fun α => α.1 ∈ S)
      rw [activeDeg, degree]; omega
    have hterm : ∀ α ∈ (G.inDarts i).filter (fun α => α.1 ∉ S),
        v (Sum.inl (rev α)) * ∏ δ ∈ (G.inDarts i).erase α, G.limitCoords S F (rev δ) =
          v (Sum.inr i) * ((-1) ^ G.activeDeg S i * F i ^ (G.degree i - G.activeDeg S i - 1)) := by
      intro α hα
      have hα' := Finset.mem_filter.1 hα
      have hαi : G.head α = i := (Finset.mem_filter.1 hα'.1).2
      rw [hinactive (rev α) (by rw [rev_fst]; exact hα'.2), tail_rev, hαi,
        G.prod_limitCoords_subset S F i (Finset.erase_subset α (G.inDarts i)),
        Finset.filter_erase, Finset.filter_erase,
        Finset.erase_eq_of_notMem (by simp [hα'.2]),
        Finset.card_erase_of_mem (by simp [hα'.1, hα'.2]), hcard]
      rfl
    have hsum : ∑ α ∈ G.inDarts i, v (Sum.inl (rev α)) *
        ∏ δ ∈ (G.inDarts i).erase α, G.limitCoords S F (rev δ) =
        ((G.degree i - G.activeDeg S i : ℕ) : K) *
          (v (Sum.inr i) * ((-1) ^ G.activeDeg S i * F i ^ (G.degree i - G.activeDeg S i - 1))) := by
      rw [← Finset.sum_filter_add_sum_filter_not (G.inDarts i) (fun α => α.1 ∈ S)]
      rw [Finset.sum_eq_zero (fun α hα => by
        rw [hactive (rev α) (by rw [rev_fst]; exact (Finset.mem_filter.1 hα).2), zero_mul]),
        zero_add, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, hcard]
    rw [hsum, G.prod_limitCoords S F i] at h
    obtain ⟨m, hm⟩ : ∃ m, G.degree i = G.activeDeg S i + m := ⟨G.degree i - G.activeDeg S i, by omega⟩
    have hkS : G.activeDeg S i = G.deg S i := activeDeg_eq_deg G S i
    have hk1 : G.activeDeg S i ≠ 1 := by
      intro h1
      rw [hkS] at h1
      exact vertexLimitEq_one (β i) (F i) (hβ1 i) (h1 ▸ hF i)
    have hβi : β i = (-1) ^ G.activeDeg S i * F i ^ ((1 : ℤ) - G.activeDeg S i) := by
      rw [hkS]; exact (hF i).2
    have hbr := vertex_bracket_ne_zero (hF0 i) hk1 hβi (m := m)
    rw [hm] at h
    simp only [Nat.add_sub_cancel_left] at h
    have hFm : F i * ((m : K) * (v (Sum.inr i) *
        ((-1) ^ G.activeDeg S i * F i ^ (m - 1)))) =
        v (Sum.inr i) * ((m : K) * ((-1) ^ G.activeDeg S i * F i ^ m)) := by
      rcases m with _ | m
      · simp
      · simp only [Nat.add_sub_cancel]
        rw [pow_succ]
        ring
    have e : v (Sum.inr i) * ((-1) ^ G.activeDeg S i * F i ^ m -
          β i * ((G.activeDeg S i + m : ℕ) : K) * F i ^ (G.activeDeg S i + m - 1)) +
        F i * ((m : K) * (v (Sum.inr i) * ((-1) ^ G.activeDeg S i * F i ^ (m - 1)))) =
        v (Sum.inr i) * ((-1) ^ G.activeDeg S i * F i ^ m -
          β i * ((G.activeDeg S i + m : ℕ) : K) * F i ^ (G.activeDeg S i + m - 1) +
          (m : K) * ((-1) ^ G.activeDeg S i * F i ^ m)) := by
      rw [hFm]; ring
    rw [e] at h
    rcases mul_eq_zero.1 h with h1 | h1
    · exact h1
    · exact absurd h1 hbr
  funext w
  rcases w with α | i
  · by_cases hα : α.1 ∈ S
    · exact hactive α hα
    · rw [hinactive α hα, hvert]; rfl
  · exact hvert i

end Multigraph

end BPFixedPoints
