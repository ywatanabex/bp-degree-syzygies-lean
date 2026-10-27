import BPFixedPoints.StrongField.AnalyticGerm
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Monomial division in ℂ{w} and the analytic boundary algebra (`sf:boundary-algebra`)

This file identifies the polynomial boundary algebra ℂ[w]/(w_i^{r_i}) of
`StrongField/BoundaryAlgebra.lean` with the analytic local algebra ℂ{w}/(w_i^{r_i}), where
ℂ{w} = `analyticGerms V` is the algebra of analytic germs at 0 of `StrongField/AnalyticGerm.lean`.

* **Division by one coordinate** (`exists_eventuallyEq_killCoord_add`): if f is analytic at 0,
  then f(y) = f(y|_{y_i=0}) + y_i h(y) near 0 with h analytic at 0. The function h is the sum of an
  explicit power series (`divSeries`): the n-th term is the telescoping sum
  ∑_k p_{n+1}(Ly,…,Ly,e_i,y,…,y) (`divTerm`, `smul_divTerm_apply_const`), whose norm is at most
  (n+1)‖p_{n+1}‖ (`norm_divTerm_le`), so its radius is positive (`radius_divSeries_pos`). This is
  the version with parameters of the one-variable `AnalyticAt.exists_eventuallyEq_sum_add_pow_mul`;
  the coefficient functions are jointly analytic.
* **Existence** (`surjective_toTruncQuot`, `exists_eventuallyEq_box_add`): every analytic germ is
  congruent modulo (w_i^{r_i}) to a polynomial, and then to a polynomial supported in the box
  {a | a_i < r_i}. The proof divides by one coordinate at a time, projecting onto growing sets of
  coordinates.
* **Uniqueness** (`ker_toTruncQuot`, `eq_zero_of_aeval_mem_truncGermIdeal`,
  `eq_zero_of_eventuallyEq`): the difference quotients Δ_i φ = (φ − φ|_{w_i=0})/w_i (`divCoord`,
  well defined since w_i is a nonzerodivisor) give coefficient functionals
  L_l = (value at 0) ∘ Δ_{l_0} ∘ ⋯ (`taylorCoeff`). On polynomials L_l reads off the coefficient
  of w^{count(l)} (`taylorCoeff_aeval`), and it vanishes on (w_i^{r_i}) when l contains each i fewer
  than r_i times (`taylorCoeff_eq_zero_of_mem`). No derivatives are used.
* **The isomorphism** `truncQuotEquiv r : ℂ{w}/(w_i^{r_i}) ≃ₐ[ℂ] ℂ[w]/(w_i^{r_i})` is induced by
  polynomial evaluation (`truncQuotEquiv_symm_mk`) and sends w_i to X_i (`truncQuotEquiv_mk_coord`).
  Consequences: the monomial basis `truncGermBasis`, dimension and length ∏ r_i
  (`finrank_truncGermQuot`, `length_truncGermQuot`), locality (`isLocalRing_truncGermQuot`).
* **Complete intersection in ℂ{w}** (`isRegular_unit_mul_coord_pow`,
  `isRegular_toList_map_coord_pow`): for r_i > 0, unit multiples of the powers w_i^{r_i}, each
  variable listed once, form a regular sequence in ℂ{w} itself, by a colon argument with Δ_j
  (`mem_truncGermIdealOn_of_coord_mul_mem`).

Not covered here: general convergent power series and Weierstrass division or preparation. The
free basis over the parameter ring ℂ{p} is in `AnalyticFamily.lean`.
-/

set_option linter.unusedSectionVars false

open Filter Topology MvPolynomial

namespace BPFixedPoints

namespace BoundaryAlgebra

section Multilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The divided-difference term of a multilinear map in n+1 variables: the sum over positions k of
f(L v_0, …, L v_{k−1}, e, v_k, …, v_{n−1}). On the diagonal, c times it is the difference
f(y,…,y) − f(Ly,…,Ly) whenever y − Ly = c e (`smul_divTerm_apply_const`). -/
noncomputable def divTerm (L : E →L[ℂ] E) (e : E) {n : ℕ}
    (f : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => E) ℂ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => E) ℂ :=
  ∑ k : Fin (n + 1), (f.curryMid k e).compContinuousLinearMap
    (fun j : Fin n => if (j : ℕ) < k then L else ContinuousLinearMap.id ℂ E)

/-- The vector with first k entries z and remaining entries y. -/
private def stair (y z : E) (n k : ℕ) : Fin (n + 1) → E :=
  fun j => if (j : ℕ) < k then z else y

/-- Inserting x at position k into the reduced staircase vector. -/
private theorem insertNth_stair (y z x : E) {n : ℕ} (k : Fin (n + 1)) :
    k.insertNth x (fun j : Fin n => if (j : ℕ) < k then z else y) =
      Function.update (stair y z n k) k x := by
  ext j
  rcases Fin.eq_self_or_eq_succAbove k j with rfl | ⟨j, rfl⟩
  · simp
  · rw [Fin.insertNth_apply_succAbove, Function.update_of_ne (Fin.succAbove_ne k j)]
    by_cases h : (j : ℕ) < k
    · rw [Fin.succAbove_of_castSucc_lt k j (by rw [Fin.lt_def]; simpa using h)]
      simp [stair, h]
    · rw [Fin.succAbove_of_le_castSucc k j (by rw [Fin.le_def]; simp; omega)]
      have h' : ¬ ((j : ℕ) + 1 < k) := by omega
      simp [stair, h, h']

/-- Putting y at position k does not change the k-th staircase vector. -/
private theorem update_stair_self (y z : E) {n : ℕ} (k : Fin (n + 1)) :
    Function.update (stair y z n k) k y = stair y z n k := by
  ext j
  by_cases h : j = k
  · subst h; simp [stair]
  · rw [Function.update_of_ne h]

/-- Putting z at position k turns the k-th staircase vector into the (k+1)-th. -/
private theorem update_stair_succ (y z : E) {n : ℕ} (k : Fin (n + 1)) :
    Function.update (stair y z n k) k z = stair y z n ((k : ℕ) + 1) := by
  ext j
  by_cases h : j = k
  · subst h; simp [stair]
  · rw [Function.update_of_ne h]
    have : (j : ℕ) ≠ k := fun h' => h (Fin.ext h')
    simp only [stair]
    split_ifs <;> first | rfl | omega

/-- **Telescoping identity.** If y − Ly = c e, then
c · divTerm(f)(y,…,y) = f(y,…,y) − f(Ly,…,Ly). -/
theorem smul_divTerm_apply_const (L : E →L[ℂ] E) (e : E) {n : ℕ}
    (f : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => E) ℂ) (y : E) (c : ℂ)
    (hy : y - L y = c • e) :
    c * divTerm L e f (fun _ => y) = f (fun _ => y) - f (fun _ => L y) := by
  have hterm : ∀ k : Fin (n + 1), c * ((f.curryMid k e).compContinuousLinearMap
      (fun j : Fin n => if (j : ℕ) < k then L else ContinuousLinearMap.id ℂ E)) (fun _ => y) =
      f (stair y (L y) n k) - f (stair y (L y) n ((k : ℕ) + 1)) := by
    intro k
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.curryMid_apply]
    have hm : (fun j : Fin n => (if (j : ℕ) < k then L else ContinuousLinearMap.id ℂ E) y) =
        fun j : Fin n => if (j : ℕ) < k then L y else y := by
      funext j; split_ifs <;> simp
    rw [hm, insertNth_stair, ← smul_eq_mul, ← f.map_update_smul, ← hy, f.map_update_sub,
      update_stair_self, update_stair_succ]
  simp only [divTerm, sum_apply, Finset.mul_sum, hterm]
  rw [Fin.sum_univ_eq_sum_range
      (fun k => f (stair y (L y) n k) - f (stair y (L y) n ((k : ℕ) + 1))),
    Finset.sum_range_sub']
  have h0 : stair y (L y) n 0 = fun _ => y := by funext j; simp [stair]
  have h1 : stair y (L y) n (n + 1) = fun _ => L y := by
    funext j; have := j.2; simp only [stair]; split_ifs; rfl
  rw [h0, h1]

/-- Norm bound for the divided-difference term when ‖L‖ ≤ 1 and ‖e‖ ≤ 1. -/
theorem norm_divTerm_le (L : E →L[ℂ] E) (e : E) (hL : ‖L‖ ≤ 1) (he : ‖e‖ ≤ 1) {n : ℕ}
    (f : ContinuousMultilinearMap ℂ (fun _ : Fin (n + 1) => E) ℂ) :
    ‖divTerm L e f‖ ≤ (n + 1) * ‖f‖ := by
  have hk : ∀ k : Fin (n + 1), ‖(f.curryMid k e).compContinuousLinearMap
      (fun j : Fin n => if (j : ℕ) < k then L else ContinuousLinearMap.id ℂ E)‖ ≤ ‖f‖ := by
    intro k
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hprod : ∏ j : Fin n, ‖(if (j : ℕ) < k then L else ContinuousLinearMap.id ℂ E)‖ ≤ 1 :=
      Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => by
        split_ifs
        · exact hL
        · exact ContinuousLinearMap.norm_id_le
    have hc : ‖f.curryMid k e‖ ≤ ‖f‖ :=
      ((f.curryMid k).le_opNorm e).trans
        (by
          have : ‖f.curryMid k‖ ≤ ‖f‖ :=
            MultilinearMap.mkContinuousLinear_norm_le _ (norm_nonneg f) _
          calc ‖f.curryMid k‖ * ‖e‖ ≤ ‖f‖ * 1 :=
                mul_le_mul this he (norm_nonneg _) (norm_nonneg _)
            _ = ‖f‖ := mul_one _)
    calc ‖f.curryMid k e‖ * ∏ j : Fin n, ‖(if (j : ℕ) < k then L else ContinuousLinearMap.id ℂ E)‖
        ≤ ‖f‖ * 1 := mul_le_mul hc hprod (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          (norm_nonneg _)
      _ = ‖f‖ := mul_one _
  calc ‖divTerm L e f‖ ≤ ∑ k : Fin (n + 1), ‖(f.curryMid k e).compContinuousLinearMap
        (fun j : Fin n => if (j : ℕ) < k then L else ContinuousLinearMap.id ℂ E)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _k : Fin (n + 1), ‖f‖ := Finset.sum_le_sum fun k _ => hk k
    _ = (n + 1) * ‖f‖ := by simp

end Multilinear

section KillCoord

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The projection y ↦ y with the i-th coordinate replaced by 0. -/
noncomputable def killCoord (i : V) : (V → ℂ) →L[ℂ] (V → ℂ) :=
  ContinuousLinearMap.pi fun j => if j = i then 0 else ContinuousLinearMap.proj j

/-- `killCoord i y` is y with y_i replaced by 0. -/
theorem killCoord_apply (i : V) (y : V → ℂ) : killCoord i y = Function.update y i 0 := by
  funext j
  by_cases h : j = i
  · subst h; simp [killCoord]
  · simp [killCoord, h]

/-- `killCoord i` does not increase the sup norm. -/
theorem norm_killCoord_apply_le (i : V) (y : V → ℂ) : ‖killCoord i y‖ ≤ ‖y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg y)).2 fun j => ?_
  rw [killCoord_apply]
  by_cases h : j = i
  · subst h; simp
  · rw [Function.update_of_ne h]; exact norm_le_pi_norm y j

/-- `killCoord i` has operator norm at most 1. -/
theorem norm_killCoord_le (i : V) : ‖killCoord i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [one_mul]; exact norm_killCoord_apply_le i y

/-- y − `killCoord i` y = y_i e_i. -/
theorem sub_killCoord (i : V) (y : V → ℂ) :
    y - killCoord i y = y i • Pi.single i (1 : ℂ) := by
  funext j
  rw [killCoord_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- The divided-difference power series of p in the i-th coordinate direction. -/
noncomputable def divSeries (i : V) (p : FormalMultilinearSeries ℂ (V → ℂ) ℂ) :
    FormalMultilinearSeries ℂ (V → ℂ) ℂ :=
  fun n => divTerm (killCoord i) (Pi.single i 1) (p (n + 1))

/-- The divided-difference series has positive radius whenever p does: from ‖p_n‖ r^n ≤ C one
gets ‖divSeries_n‖ (r/2)^n ≤ (n+1) 2^{−n} C / r ≤ C / r. -/
theorem radius_divSeries_pos (i : V) {p : FormalMultilinearSeries ℂ (V → ℂ) ℂ}
    (hp : 0 < p.radius) : 0 < (divSeries i p).radius := by
  obtain ⟨r, hr0, hrp⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp
  obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius hrp
  have hr : (0 : ℝ) < r := by exact_mod_cast hr0
  have hbound : ∀ n, ‖divSeries i p n‖ * ((r / 2 : NNReal) : ℝ) ^ n ≤ C / r := by
    intro n
    have h1 : ‖divSeries i p n‖ ≤ (n + 1) * ‖p (n + 1)‖ :=
      norm_divTerm_le _ _ (norm_killCoord_le i) (by rw [Pi.norm_single, norm_one]) _
    have h2 : ((n : ℝ) + 1) ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
    have h3 := hC (n + 1)
    rw [le_div_iff₀ hr]
    have e : ((n : ℝ) + 1) * ‖p (n + 1)‖ * ((r : ℝ) / 2) ^ n * r =
        ((n + 1) / 2 ^ n) * (‖p (n + 1)‖ * (r : ℝ) ^ (n + 1)) := by
      rw [div_pow, pow_succ]
      ring
    calc ‖divSeries i p n‖ * ((r / 2 : NNReal) : ℝ) ^ n * r
        ≤ ((n : ℝ) + 1) * ‖p (n + 1)‖ * ((r : ℝ) / 2) ^ n * r := by
          push_cast
          gcongr
      _ = ((n + 1) / 2 ^ n) * (‖p (n + 1)‖ * (r : ℝ) ^ (n + 1)) := e
      _ ≤ 1 * C := by
          gcongr
          · rw [div_le_one (by positivity)]; exact h2
      _ = C := one_mul C
  refine lt_of_lt_of_le ?_ ((divSeries i p).le_radius_of_bound (C / r) hbound)
  exact ENNReal.coe_pos.2 (half_pos (ENNReal.coe_pos.1 hr0))

/-- **Division by one coordinate.** If f is analytic at 0, then near 0,
f(y) = f(y with y_i = 0) + y_i h(y) for some h analytic at 0. The function h is the sum of the
divided-difference power series. -/
theorem exists_eventuallyEq_killCoord_add {f : (V → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (i : V) :
    ∃ h : (V → ℂ) → ℂ, AnalyticAt ℂ h 0 ∧
      ∀ᶠ y in 𝓝 0, f y = f (killCoord i y) + y i * h y := by
  obtain ⟨p, R, hfp⟩ := hf
  have hq := radius_divSeries_pos i (hfp.r_pos.trans_le hfp.r_le)
  refine ⟨(divSeries i p).sum, ((divSeries i p).hasFPowerSeriesOnBall hq).analyticAt, ?_⟩
  filter_upwards [Metric.eball_mem_nhds (0 : V → ℂ) (lt_min hfp.r_pos hq)] with y hy
  have hyR : y ∈ Metric.eball (0 : V → ℂ) R := Metric.eball_subset_eball (min_le_left _ _) hy
  have hyq : y ∈ Metric.eball (0 : V → ℂ) (divSeries i p).radius :=
    Metric.eball_subset_eball (min_le_right _ _) hy
  have hLyR : killCoord i y ∈ Metric.eball (0 : V → ℂ) R := by
    rw [Metric.mem_eball] at hyR ⊢
    refine lt_of_le_of_lt ?_ hyR
    rw [edist_dist, edist_dist, dist_zero_right, dist_zero_right]
    exact ENNReal.ofReal_le_ofReal (norm_killCoord_apply_le i y)
  have h1 := (hasSum_nat_add_iff' 1).2 (hfp.hasSum hyR)
  have h2 := (hasSum_nat_add_iff' 1).2 (hfp.hasSum hLyR)
  have h3 := ((divSeries i p).hasSum hyq).mul_left (y i)
  have h4 : HasSum (fun n => y i * divSeries i p n (fun _ => y))
      (f (0 + y) - f (0 + killCoord i y)) := by
    have h5 := h1.sub h2
    have hp0 : p 0 (fun _ => y) = p 0 (fun _ => killCoord i y) :=
      congrArg (p 0) (Subsingleton.elim _ _)
    simp only [Finset.sum_range_one, hp0, sub_sub_sub_cancel_right] at h5
    convert h5 using 1
    funext n
    exact smul_divTerm_apply_const _ _ _ y (y i) (sub_killCoord i y)
  rw [zero_add, zero_add] at h4
  have := h3.unique h4
  linear_combination -this

end KillCoord

section Existence

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restriction of germs to the hyperplane w_i = 0, extended constantly in w_i: the pullback along
`killCoord i`. -/
noncomputable def restrictCoord (i : V) : analyticGerms V →ₐ[ℂ] analyticGerms V :=
  pullback (killCoord i) ((killCoord i).analyticAt 0) (map_zero _)

/-- The restriction kills w_i and fixes the other coordinate germs. -/
theorem restrictCoord_coord (i j : V) :
    restrictCoord i (coord j) = if j = i then 0 else coord j := by
  unfold coord restrictCoord
  rw [pullback_germOf]
  split_ifs with h
  · subst h
    exact germOf_congr _ analyticAt_const fun y => by simp [killCoord_apply]
  · exact germOf_congr _ _ fun y => by simp [killCoord_apply, h]

/-- **Division by one coordinate, germ form.** Every analytic germ is φ = φ|_{w_i=0} + w_i ψ. -/
theorem exists_eq_restrictCoord_add (i : V) (φ : analyticGerms V) :
    ∃ ψ, φ = restrictCoord i φ + coord i * ψ := by
  obtain ⟨f, hf, rfl⟩ := exists_germOf φ
  obtain ⟨h, hh, heq⟩ := exists_eventuallyEq_killCoord_add hf i
  refine ⟨germOf h hh, ?_⟩
  exact ((germOf_eq_iff hf ((analyticAt_comp_zero hf ((killCoord i).analyticAt 0)
    (map_zero _)).fun_add ((analyticAt_coord i 0).fun_mul hh))).2 heq).trans rfl

/-- The projection onto the coordinates in T: y ↦ (y_j if j ∈ T, 0 otherwise). -/
noncomputable def projOn (T : Finset V) : (V → ℂ) →L[ℂ] (V → ℂ) :=
  ContinuousLinearMap.pi fun j => if j ∈ T then ContinuousLinearMap.proj j else 0

/-- Coordinates of the projection onto T. -/
theorem projOn_apply (T : Finset V) (y : V → ℂ) (j : V) :
    projOn T y j = if j ∈ T then y j else 0 := by
  by_cases h : j ∈ T <;> simp [projOn, h]

/-- Restriction of germs to the coordinate subspace of T, extended constantly in the other
coordinates: the pullback along `projOn T`. -/
noncomputable def restrictTo (T : Finset V) : analyticGerms V →ₐ[ℂ] analyticGerms V :=
  pullback (projOn T) ((projOn T).analyticAt 0) (map_zero _)

/-- Restricting to no coordinates gives the constant germ. -/
theorem restrictTo_empty (φ : analyticGerms V) :
    restrictTo ∅ φ = algebraMap ℂ (analyticGerms V) (evalZero φ) := by
  obtain ⟨f, hf, rfl⟩ := exists_germOf φ
  unfold restrictTo
  rw [pullback_germOf, evalZero_germOf, ← germOf_const _ analyticAt_const]
  refine germOf_congr _ _ fun y => ?_
  have hy : projOn (∅ : Finset V) y = 0 := by funext j; simp [projOn_apply]
  rw [hy]

/-- Restricting to all coordinates is the identity. -/
theorem restrictTo_univ (φ : analyticGerms V) : restrictTo Finset.univ φ = φ :=
  pullback_eq_self _ _ (Eventually.of_forall fun y => by funext j; simp [projOn_apply]) φ

/-- Restricting to w_i = 0 and then to T ∪ {i} is restricting to T, if i ∉ T. -/
theorem restrictTo_restrictCoord {T : Finset V} {i : V} (hi : i ∉ T) (φ : analyticGerms V) :
    restrictTo (insert i T) (restrictCoord i φ) = restrictTo T φ := by
  have hc : AnalyticAt ℂ (fun x => killCoord i (projOn (insert i T) x)) 0 :=
    ((killCoord i).comp (projOn (insert i T))).analyticAt 0
  unfold restrictTo restrictCoord
  rw [pullback_pullback (projOn (insert i T)) _ _ (killCoord i) _ _ hc (by simp)]
  refine pullback_congr ?_ _ _ _ _ φ
  funext y j
  rw [killCoord_apply, projOn_apply]
  by_cases hj : j = i
  · subst hj; simp [hi]
  · rw [Function.update_of_ne hj, projOn_apply]
    simp [Finset.mem_insert, hj]

/-- Restricting to a set containing i fixes the coordinate germ w_i. -/
theorem restrictTo_coord {T : Finset V} {i : V} (hi : i ∈ T) :
    restrictTo T (coord i) = coord i := by
  unfold coord restrictTo
  rw [pullback_germOf]
  exact germOf_congr _ _ fun y => by simp [projOn_apply, hi]

omit [DecidableEq V] in
/-- Polynomial evaluation followed by reduction: ℂ[w] → ℂ{w}/(w_i^{r_i}). -/
noncomputable def toTruncQuot (r : V → ℕ) :
    MvPolynomial V ℂ →ₐ[ℂ] analyticGerms V ⧸ truncGermIdeal r :=
  (Ideal.Quotient.mkₐ ℂ (truncGermIdeal r)).comp (aeval coord)

omit [DecidableEq V] in
/-- `toTruncQuot r P` is the class of the germ of P. -/
theorem toTruncQuot_apply (r : V → ℕ) (P : MvPolynomial V ℂ) :
    toTruncQuot r P = Ideal.Quotient.mk (truncGermIdeal r) (aeval coord P) := rfl

omit [DecidableEq V] in
/-- **Monomial division, existence.** Every analytic germ is congruent modulo (w_i^{r_i}) to a
polynomial. The proof projects onto growing sets of coordinates and divides by one coordinate at a
time. -/
theorem surjective_toTruncQuot (r : V → ℕ) : Function.Surjective (toTruncQuot r) := by
  classical
  intro x
  obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- 𝒮: the germs congruent to a polynomial modulo the truncation ideal.
  set 𝒮 : Subalgebra ℂ (analyticGerms V) :=
    (toTruncQuot r).range.comap (Ideal.Quotient.mkₐ ℂ (truncGermIdeal r))
  have hI : ∀ ψ ∈ truncGermIdeal r, ψ ∈ 𝒮 := fun ψ hψ =>
    ⟨0, by rw [map_zero]; exact ((Ideal.Quotient.eq_zero_iff_mem).2 hψ).symm⟩
  have hX : ∀ i, coord i ∈ 𝒮 := fun i => ⟨X i, by
    change toTruncQuot r (X i) = _
    rw [toTruncQuot_apply, aeval_X]
    rfl⟩
  suffices h : ∀ T : Finset V, ∀ φ : analyticGerms V, restrictTo T φ ∈ 𝒮 by
    have := h Finset.univ φ
    rw [restrictTo_univ] at this
    obtain ⟨P, hP⟩ := this
    exact ⟨P, hP⟩
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro φ
    rw [restrictTo_empty]
    exact algebraMap_mem 𝒮 _
  | insert i T hi ih =>
    have key : ∀ n : ℕ, ∀ φ : analyticGerms V, ∃ g : analyticGerms V,
        restrictTo (insert i T) φ - coord i ^ n * g ∈ 𝒮 := by
      intro n
      induction n with
      | zero =>
        intro φ
        refine ⟨restrictTo (insert i T) φ, ?_⟩
        rw [pow_zero, one_mul, sub_self]
        exact zero_mem _
      | succ n ihn =>
        intro φ
        obtain ⟨ψ, hψ⟩ := exists_eq_restrictCoord_add i φ
        obtain ⟨g, hg⟩ := ihn ψ
        refine ⟨g, ?_⟩
        have e : restrictTo (insert i T) φ =
            restrictTo T φ + coord i * restrictTo (insert i T) ψ := by
          conv_lhs => rw [hψ]
          rw [map_add, map_mul, restrictTo_restrictCoord hi,
            restrictTo_coord (Finset.mem_insert_self i T)]
        rw [e, pow_succ', mul_assoc, add_sub_assoc, ← mul_sub]
        exact add_mem (ih φ) (mul_mem (hX i) hg)
    intro φ
    obtain ⟨g, hg⟩ := key (r i) φ
    have hg' : coord i ^ r i * g ∈ 𝒮 :=
      hI _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩))
    have := add_mem hg hg'
    rwa [sub_add_cancel] at this

end Existence

section Uniqueness

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every germ minus its restriction to w_i = 0 is divisible by w_i. -/
theorem exists_coord_mul_eq_sub (i : V) (φ : analyticGerms V) :
    ∃ ψ, coord i * ψ = φ - restrictCoord i φ := by
  obtain ⟨ψ, hψ⟩ := exists_eq_restrictCoord_add i φ
  exact ⟨ψ, eq_sub_of_add_eq' hψ.symm⟩

/-- The difference quotient Δ_i φ = (φ − φ|_{w_i=0}) / w_i, a ℂ-linear operator on ℂ{w}. It is
well defined because w_i is a nonzerodivisor. -/
noncomputable def divCoord (i : V) : analyticGerms V →ₗ[ℂ] analyticGerms V where
  toFun φ := (exists_coord_mul_eq_sub i φ).choose
  map_add' φ ψ := coord_mul_cancel (by
    rw [mul_add, (exists_coord_mul_eq_sub i (φ + ψ)).choose_spec,
      (exists_coord_mul_eq_sub i φ).choose_spec, (exists_coord_mul_eq_sub i ψ).choose_spec,
      map_add]
    ring)
  map_smul' c φ := coord_mul_cancel (by
    rw [RingHom.id_apply, mul_smul_comm, (exists_coord_mul_eq_sub i (c • φ)).choose_spec,
      (exists_coord_mul_eq_sub i φ).choose_spec, map_smul, smul_sub])

/-- Defining property of the difference quotient. -/
theorem coord_mul_divCoord (i : V) (φ : analyticGerms V) :
    coord i * divCoord i φ = φ - restrictCoord i φ :=
  (exists_coord_mul_eq_sub i φ).choose_spec

/-- Characterization of the difference quotient. -/
theorem divCoord_eq_of {i : V} {φ ψ : analyticGerms V} (h : coord i * ψ = φ - restrictCoord i φ) :
    divCoord i φ = ψ :=
  coord_mul_cancel ((coord_mul_divCoord i φ).trans h.symm)

/-- Δ_i(w_i^m ψ) = w_i^{m−1} ψ for m ≥ 1. -/
theorem divCoord_coord_pow_mul {i : V} {m : ℕ} (hm : m ≠ 0) (ψ : analyticGerms V) :
    divCoord i (coord i ^ m * ψ) = coord i ^ (m - 1) * ψ := by
  apply divCoord_eq_of
  rw [map_mul, map_pow, restrictCoord_coord, ite_eq_left rfl, zero_pow hm, zero_mul, sub_zero,
    ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm)]

/-- Δ_j(w_i^m ψ) = w_i^m Δ_j ψ for j ≠ i. -/
theorem divCoord_coord_pow_mul_of_ne {i j : V} (hji : j ≠ i) (m : ℕ) (ψ : analyticGerms V) :
    divCoord j (coord i ^ m * ψ) = coord i ^ m * divCoord j ψ := by
  apply divCoord_eq_of
  rw [map_mul, map_pow, restrictCoord_coord, ite_eq_right (Ne.symm hji), mul_left_comm,
    coord_mul_divCoord, mul_sub]

/-- The monomial germ w^β = ∏_j w_j^{β_j}. -/
noncomputable def monoGerm (β : V →₀ ℕ) : analyticGerms V := ∏ j, coord j ^ β j

/-- Polynomial evaluation of a monomial. -/
theorem aeval_monomial_coord (β : V →₀ ℕ) (c : ℂ) :
    aeval coord (monomial β c) = c • monoGerm β := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Algebra.smul_def]
  rfl

/-- Restriction of a monomial germ to w_i = 0. -/
theorem restrictCoord_monoGerm (i : V) (β : V →₀ ℕ) :
    restrictCoord i (monoGerm β) = if β i = 0 then monoGerm β else 0 := by
  rw [monoGerm, map_prod]
  split_ifs with h
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_pow, restrictCoord_coord]
    split_ifs with hj
    · subst hj; rw [h, pow_zero, pow_zero]
    · rfl
  · refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [map_pow, restrictCoord_coord, ite_eq_left rfl, zero_pow h]

/-- If β_i ≠ 0, then w^β = w_i w^{β − e_i}. -/
theorem monoGerm_eq_coord_mul {i : V} {β : V →₀ ℕ} (h : β i ≠ 0) :
    monoGerm β = coord i * monoGerm (β - Finsupp.single i 1) := by
  rw [monoGerm, monoGerm, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← mul_assoc]
  congr 1
  · rw [← pow_succ']
    congr 1
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  · refine Finset.prod_congr rfl fun j hj => ?_
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [Ne.symm hji]

/-- Δ_i on monomial germs. -/
theorem divCoord_monoGerm (i : V) (β : V →₀ ℕ) :
    divCoord i (monoGerm β) = if β i = 0 then 0 else monoGerm (β - Finsupp.single i 1) := by
  split_ifs with h
  · apply divCoord_eq_of
    rw [restrictCoord_monoGerm, ite_eq_left h, mul_zero, sub_self]
  · apply divCoord_eq_of
    rw [restrictCoord_monoGerm, ite_eq_right h, sub_zero, ← monoGerm_eq_coord_mul h]

/-- Value of a monomial germ at the origin. -/
theorem evalZero_monoGerm (γ : V →₀ ℕ) : evalZero (monoGerm γ) = if γ = 0 then 1 else 0 := by
  rw [monoGerm, map_prod]
  simp only [map_pow, evalZero_coord]
  split_ifs with h
  · subst h; simp
  · obtain ⟨j, hj⟩ := Finsupp.ne_iff.1 h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (zero_pow hj)

/-- The exponent vector of a list of coordinates: j ↦ number of occurrences of j. -/
noncomputable def listCount (l : List V) : V →₀ ℕ := (l.map fun j => Finsupp.single j 1).sum

/-- The empty list has exponent vector 0. -/
theorem listCount_nil : listCount ([] : List V) = 0 := rfl

/-- Adding j to a list adds e_j to its exponent vector. -/
theorem listCount_cons (j : V) (l : List V) :
    listCount (j :: l) = Finsupp.single j 1 + listCount l := by
  simp [listCount]

/-- Every exponent vector is the exponent vector of some list. -/
theorem exists_listCount_eq (α : V →₀ ℕ) : ∃ l : List V, listCount l = α := by
  induction α using Finsupp.induction with
  | zero => exact ⟨[], rfl⟩
  | single_add a b f _ _ ih =>
    obtain ⟨l, hl⟩ := ih
    refine ⟨List.replicate b a ++ l, ?_⟩
    simp [listCount, List.map_replicate, List.sum_replicate] at *
    rw [← hl]

/-- The iterated difference quotient Δ_l = Δ_{l_0} ∘ ⋯ ∘ Δ_{l_{k−1}}. -/
noncomputable def divCoordList : List V → analyticGerms V →ₗ[ℂ] analyticGerms V
  | [] => LinearMap.id
  | j :: l => divCoord j ∘ₗ divCoordList l

/-- Iterated difference quotients of a monomial germ. -/
theorem divCoordList_monoGerm (l : List V) (β : V →₀ ℕ) :
    divCoordList l (monoGerm β) =
      if listCount l ≤ β then monoGerm (β - listCount l) else 0 := by
  induction l with
  | nil => simp [divCoordList, listCount_nil]
  | cons j l ih =>
    change divCoord j (divCoordList l (monoGerm β)) = _
    rw [ih, listCount_cons]
    by_cases h : listCount l ≤ β
    · rw [ite_eq_left h, divCoord_monoGerm]
      by_cases h2 : (β - listCount l) j = 0
      · rw [ite_eq_left h2, ite_eq_right]
        intro hle
        have h3 := Finsupp.le_def.1 hle j
        simp only [Finsupp.tsub_apply] at h2
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at h3
        omega
      · have hle : Finsupp.single j 1 + listCount l ≤ β := by
          rw [Finsupp.le_def]
          intro k
          have := Finsupp.le_def.1 h k
          simp only [Finsupp.tsub_apply] at h2
          simp only [Finsupp.add_apply, Finsupp.single_apply]
          split_ifs with hk
          · subst hk; omega
          · omega
        rw [ite_eq_right h2, ite_eq_left hle]
        congr 1
        ext k
        simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
        split_ifs <;> omega
    · rw [ite_eq_right h, map_zero, ite_eq_right]
      intro hle
      exact h (le_trans le_add_self hle)

/-- **Coefficient functional.** L_l = (value at 0) ∘ Δ_l. On polynomials it extracts the
coefficient of the monomial w^{listCount l}. -/
noncomputable def taylorCoeff (l : List V) : analyticGerms V →ₗ[ℂ] ℂ :=
  evalZero.toLinearMap ∘ₗ divCoordList l

/-- L_l(w^β) = 1 if β = count(l), and 0 otherwise. -/
theorem taylorCoeff_monoGerm (l : List V) (β : V →₀ ℕ) :
    taylorCoeff l (monoGerm β) = if β = listCount l then 1 else 0 := by
  change evalZero (divCoordList l (monoGerm β)) = _
  rw [divCoordList_monoGerm]
  by_cases h : listCount l ≤ β
  · rw [ite_eq_left h, evalZero_monoGerm]
    by_cases h2 : β = listCount l
    · rw [ite_eq_left h2, ite_eq_left (by rw [h2, tsub_self])]
    · rw [ite_eq_right h2, ite_eq_right]
      intro h3
      exact h2 (le_antisymm (tsub_eq_zero_iff_le.1 h3) h)
  · rw [ite_eq_right h, map_zero, ite_eq_right]
    rintro rfl
    exact h le_rfl

/-- L_l extracts polynomial coefficients. -/
theorem taylorCoeff_aeval (l : List V) (P : MvPolynomial V ℂ) :
    taylorCoeff l (aeval coord P) = P.coeff (listCount l) := by
  induction P using MvPolynomial.induction_on' with
  | monomial β c =>
    rw [aeval_monomial_coord, map_smul, taylorCoeff_monoGerm, coeff_monomial, smul_eq_mul]
    split_ifs <;> simp
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ]; simp

/-- Iterated difference quotients of w_i^m ψ keep a factor w_i^{m − (number of i in l)}. -/
theorem exists_divCoordList_coord_pow_mul (i : V) {m : ℕ} (ψ : analyticGerms V) (l : List V)
    (hl : listCount l i < m) :
    ∃ ψ', divCoordList l (coord i ^ m * ψ) = coord i ^ (m - listCount l i) * ψ' := by
  induction l with
  | nil => exact ⟨ψ, by simp [divCoordList, listCount_nil]⟩
  | cons j l ih =>
    rw [listCount_cons, Finsupp.add_apply] at hl
    obtain ⟨ψ', hψ'⟩ := ih (by omega)
    change ∃ ψ'', divCoord j (divCoordList l (coord i ^ m * ψ)) = _
    rw [hψ', listCount_cons, Finsupp.add_apply]
    by_cases hji : j = i
    · subst hji
      refine ⟨ψ', ?_⟩
      rw [divCoord_coord_pow_mul (by omega), Finsupp.single_eq_same]
      congr 2
      omega
    · refine ⟨divCoord j ψ', ?_⟩
      rw [divCoord_coord_pow_mul_of_ne hji, Finsupp.single_eq_of_ne (Ne.symm hji), zero_add]

/-- **L_l vanishes on the truncation ideal** when l contains each i fewer than r_i times. -/
theorem taylorCoeff_eq_zero_of_mem {r : V → ℕ} {l : List V} (hl : ∀ i, listCount l i < r i)
    {φ : analyticGerms V} (hφ : φ ∈ truncGermIdeal r) : taylorCoeff l φ = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hφ
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨ψ', hψ'⟩ := exists_divCoordList_coord_pow_mul i (c i) l (hl i)
  change evalZero (divCoordList l (c i * coord i ^ r i)) = 0
  rw [mul_comm, hψ', map_mul, map_pow, evalZero_coord, zero_pow (by have := hl i; omega),
    zero_mul]

omit [DecidableEq V] in
/-- **Monomial division, uniqueness: the kernel.** A polynomial evaluates into the germ ideal
(w_i^{r_i}) iff it lies in the polynomial truncation ideal. -/
theorem ker_toTruncQuot (r : V → ℕ) : RingHom.ker (toTruncQuot r) = truncIdeal ℂ r := by
  classical
  ext P
  rw [RingHom.mem_ker, toTruncQuot_apply, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hP
    rw [mem_truncIdeal]
    intro a ha
    by_contra hcon
    simp only [not_exists, not_le] at hcon
    obtain ⟨l, hl⟩ := exists_listCount_eq a
    have h0 := taylorCoeff_eq_zero_of_mem (l := l) (fun i => by rw [hl]; exact hcon i) hP
    rw [taylorCoeff_aeval, hl] at h0
    exact (mem_support_iff.1 ha) h0
  · exact aeval_mem_truncGermIdeal r

end Uniqueness

section Quotient

variable {V : Type*} [Fintype V]

/-- **The analytic boundary algebra is the polynomial one.** Polynomial evaluation at the
coordinate germs induces an algebra isomorphism
ℂ{w}/(w_i^{r_i}) ≃ ℂ[w]/(w_i^{r_i}), sending the class of w_i to the class of X_i
(`truncQuotEquiv_mk_coord`). -/
noncomputable def truncQuotEquiv (r : V → ℕ) :
    (analyticGerms V ⧸ truncGermIdeal r) ≃ₐ[ℂ] MvPolynomial V ℂ ⧸ truncIdeal ℂ r := by
  classical
  exact ((Ideal.quotientEquivAlgOfEq ℂ (ker_toTruncQuot r)).symm.trans
    (Ideal.quotientKerAlgEquivOfSurjective (surjective_toTruncQuot r))).symm

/-- The inverse isomorphism is induced by polynomial evaluation. -/
theorem truncQuotEquiv_symm_mk (r : V → ℕ) (P : MvPolynomial V ℂ) :
    (truncQuotEquiv r).symm (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk (truncGermIdeal r) (aeval coord P) := by
  classical
  simp only [truncQuotEquiv, AlgEquiv.symm_symm, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_symm, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]
  rfl

/-- The isomorphism sends the class of a polynomial germ to the class of the polynomial. -/
theorem truncQuotEquiv_mk_aeval (r : V → ℕ) (P : MvPolynomial V ℂ) :
    truncQuotEquiv r (Ideal.Quotient.mk (truncGermIdeal r) (aeval coord P)) =
      Ideal.Quotient.mk _ P := by
  rw [← truncQuotEquiv_symm_mk, AlgEquiv.apply_symm_apply]

/-- The isomorphism sends the coordinate germ w_i to X_i. -/
theorem truncQuotEquiv_mk_coord (r : V → ℕ) (i : V) :
    truncQuotEquiv r (Ideal.Quotient.mk (truncGermIdeal r) (coord i)) =
      Ideal.Quotient.mk _ (X i) := by
  rw [← truncQuotEquiv_mk_aeval, aeval_X]

/-- **Uniqueness, germ form.** A box polynomial whose germ lies in (w_i^{r_i}) is zero. -/
theorem eq_zero_of_aeval_mem_truncGermIdeal {r : V → ℕ} {P : MvPolynomial V ℂ}
    (hP : P ∈ restrictSupport ℂ (truncBox r)) (h : aeval coord P ∈ truncGermIdeal r) : P = 0 := by
  classical
  have hk : P ∈ truncIdeal ℂ r := by
    rw [← ker_toTruncQuot, RingHom.mem_ker, toTruncQuot_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h
  exact Submodule.disjoint_def.1 (isCompl_truncIdeal ℂ r).disjoint P hk hP

/-- The germ of y ↦ ∑_i y_i^{r_i} g_i(y). -/
theorem germOf_sum_pow_mul (r : V → ℕ) {g : V → (V → ℂ) → ℂ} (hg : ∀ i, AnalyticAt ℂ (g i) 0)
    (h : AnalyticAt ℂ (fun y => ∑ i, y i ^ r i * g i y) 0) :
    germOf (fun y => ∑ i, y i ^ r i * g i y) h = ∑ i, germOf (g i) (hg i) * coord i ^ r i := by
  rw [germOf_sum (f := fun i y => y i ^ r i * g i y) Finset.univ
    (fun i => ((analyticAt_coord i 0).pow (r i)).fun_mul (hg i)) h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  rfl

/-- Analyticity of y ↦ ∑_i y_i^{r_i} g_i(y). -/
theorem analyticAt_sum_pow_mul (r : V → ℕ) {g : V → (V → ℂ) → ℂ}
    (hg : ∀ i, AnalyticAt ℂ (g i) 0) : AnalyticAt ℂ (fun y => ∑ i, y i ^ r i * g i y) 0 :=
  Finset.analyticAt_fun_sum _ fun i _ => ((analyticAt_coord i 0).pow (r i)).fun_mul (hg i)

/-- **Monomial division (existence).** If f is analytic at 0 and r : V → ℕ, then near 0,
f = P + ∑_i w_i^{r_i} g_i with P a polynomial supported in the box {a | a_i < r_i} and every g_i
analytic at 0. -/
theorem exists_eventuallyEq_box_add {f : (V → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) (r : V → ℕ) :
    ∃ P ∈ restrictSupport ℂ (truncBox r), ∃ g : V → (V → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (g i) 0) ∧
      f =ᶠ[𝓝 0] fun y => eval y P + ∑ i, y i ^ r i * g i y := by
  classical
  obtain ⟨Q, hQ⟩ := surjective_toTruncQuot r (Ideal.Quotient.mk _ (germOf f hf))
  have hQ' : Q ∈ (⊤ : Submodule ℂ (MvPolynomial V ℂ)) := Submodule.mem_top
  rw [← (isCompl_truncIdeal ℂ r).sup_eq_top, Submodule.mem_sup] at hQ'
  obtain ⟨a, ha, b, hb, rfl⟩ := hQ'
  have ha' : a ∈ truncIdeal ℂ r := ha
  rw [toTruncQuot_apply, Ideal.Quotient.eq] at hQ
  have hmem : germOf f hf - aeval coord b ∈ truncGermIdeal r := by
    have := Ideal.sub_mem _ (aeval_mem_truncGermIdeal r ha') hQ
    rw [map_add] at this
    convert this using 1
    ring
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 hmem
  choose g hg hgc using fun i => exists_germOf (c i)
  refine ⟨b, hb, g, hg, ?_⟩
  have hs := analyticAt_sum_pow_mul r hg
  have hall : AnalyticAt ℂ (fun y => eval y b + ∑ i, y i ^ r i * g i y) 0 :=
    (analyticAt_eval b 0).fun_add hs
  rw [← germOf_eq_iff hf hall, germOf_add (analyticAt_eval b 0) hs hall, germOf_sum_pow_mul r hg,
    ← aeval_coord]
  rw [← sub_eq_iff_eq_add', ← hc]
  exact Finset.sum_congr rfl fun i _ => by rw [hgc]

/-- **Monomial division (uniqueness).** A polynomial supported in the box that agrees near 0 with
∑_i w_i^{r_i} g_i, g_i analytic at 0, is zero. -/
theorem eq_zero_of_eventuallyEq {r : V → ℕ} {P : MvPolynomial V ℂ}
    (hP : P ∈ restrictSupport ℂ (truncBox r)) {g : V → (V → ℂ) → ℂ}
    (hg : ∀ i, AnalyticAt ℂ (g i) 0)
    (h : (fun y => eval y P) =ᶠ[𝓝 0] fun y => ∑ i, y i ^ r i * g i y) : P = 0 := by
  refine eq_zero_of_aeval_mem_truncGermIdeal hP ?_
  rw [aeval_coord, (germOf_eq_iff _ (analyticAt_sum_pow_mul r hg)).2 h, germOf_sum_pow_mul r hg]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- **Monomial basis.** The classes of the monomial germs w^a, a in the box, form a basis of
ℂ{w}/(w_i^{r_i}). -/
noncomputable def truncGermBasis (r : V → ℕ) :
    Module.Basis (truncBox r) ℂ (analyticGerms V ⧸ truncGermIdeal r) :=
  (truncBasis ℂ r).map (truncQuotEquiv r).symm.toLinearEquiv

/-- The basis vector indexed by a is the class of the monomial germ w^a. -/
theorem truncGermBasis_apply (r : V → ℕ) (a : truncBox r) :
    truncGermBasis r a =
      Ideal.Quotient.mk (truncGermIdeal r) (aeval coord (monomial (a : V →₀ ℕ) (1 : ℂ))) := by
  rw [truncGermBasis, Module.Basis.map_apply, truncBasis_apply]
  exact truncQuotEquiv_symm_mk r _

/-- **Dimension.** dim_ℂ ℂ{w}/(w_i^{r_i}) = ∏_i r_i. -/
theorem finrank_truncGermQuot (r : V → ℕ) :
    Module.finrank ℂ (analyticGerms V ⧸ truncGermIdeal r) = ∏ i, r i :=
  (truncQuotEquiv r).toLinearEquiv.finrank_eq.trans (finrank_truncIdeal r ℂ)

/-- A ring isomorphism preserves the length of a ring over itself. -/
theorem length_self_eq_of_ringEquiv {A B : Type*} [Ring A] [Ring B] (e : A ≃+* B) :
    Module.length A A = Module.length B B := by
  have : RingHomSurjective (e : A →+* B) := ⟨e.surjective⟩
  let f : A →ₛₗ[(e : A →+* B)] B :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun a x => by simp [smul_eq_mul] }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)]

/-- **Length.** ℂ{w}/(w_i^{r_i}) has length ∏_i r_i over itself. -/
theorem length_truncGermQuot (r : V → ℕ) :
    Module.length (analyticGerms V ⧸ truncGermIdeal r) (analyticGerms V ⧸ truncGermIdeal r) =
      ((∏ i, r i : ℕ) : ℕ∞) := by
  rw [← length_truncIdeal ℂ r]
  exact length_self_eq_of_ringEquiv (truncQuotEquiv r).toRingEquiv

/-- **Local ring.** If every r_i is positive, ℂ{w}/(w_i^{r_i}) is local. -/
theorem isLocalRing_truncGermQuot {r : V → ℕ} (hr : ∀ i, 0 < r i) :
    IsLocalRing (analyticGerms V ⧸ truncGermIdeal r) := by
  have := isLocalRing ℂ r hr
  have := nontrivial_quotient ℂ r hr
  have : Nontrivial (analyticGerms V ⧸ truncGermIdeal r) :=
    (truncQuotEquiv r).symm.injective.nontrivial
  exact IsLocalRing.of_surjective' (truncQuotEquiv r).symm.toRingEquiv.toRingHom
    (truncQuotEquiv r).symm.toRingEquiv.surjective

end Quotient

section Regular

variable {V : Type*} [Fintype V]

/-- The partial truncation ideal (w_j^{r_j} : j ∈ T) of ℂ{w}. -/
noncomputable def truncGermIdealOn (r : V → ℕ) (T : Set V) : Ideal (analyticGerms V) :=
  Ideal.span ((fun j => coord j ^ r j) '' T)

/-- With all variables, the partial truncation ideal is the truncation ideal. -/
theorem truncGermIdealOn_univ (r : V → ℕ) : truncGermIdealOn r Set.univ = truncGermIdeal r := by
  rw [truncGermIdealOn, Set.image_univ, truncGermIdeal]

/-- **Colon property.** If j ∉ T, multiplication by w_j is injective modulo
(w_t^{r_t} : t ∈ T). Proof: apply the difference quotient Δ_j, which commutes with w_t, t ≠ j. -/
theorem mem_truncGermIdealOn_of_coord_mul_mem {r : V → ℕ} {T : Set V} {j : V} (hj : j ∉ T)
    {φ : analyticGerms V} (h : coord j * φ ∈ truncGermIdealOn r T) :
    φ ∈ truncGermIdealOn r T := by
  classical
  rw [truncGermIdealOn, Set.image_eq_range, Ideal.mem_span_range_iff_exists_fun] at h
  obtain ⟨c, hc⟩ := h
  have hd := congrArg (divCoord j) hc
  rw [map_sum] at hd
  have hφ : divCoord j (coord j * φ) = φ := by
    simpa using divCoord_coord_pow_mul (i := j) (m := 1) one_ne_zero φ
  rw [← hφ, ← hd, truncGermIdealOn]
  refine Ideal.sum_mem _ fun t _ => ?_
  have htj : j ≠ (t : V) := fun h => hj (h ▸ t.2)
  rw [mul_comm, divCoord_coord_pow_mul_of_ne htj]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨t, t.2, rfl⟩)

/-- If j ∉ T, multiplication by w_j^m is injective modulo (w_t^{r_t} : t ∈ T). -/
theorem mem_truncGermIdealOn_of_coord_pow_mul_mem {r : V → ℕ} {T : Set V} {j : V} (hj : j ∉ T)
    (m : ℕ) {φ : analyticGerms V} (h : coord j ^ m * φ ∈ truncGermIdealOn r T) :
    φ ∈ truncGermIdealOn r T := by
  induction m generalizing φ with
  | zero => simpa using h
  | succ m ih =>
    exact mem_truncGermIdealOn_of_coord_mul_mem hj (ih (by rwa [← mul_assoc, ← pow_succ]))

/-- Multiplying the generators by units does not change the partial truncation ideal. -/
theorem span_image_unit_mul (u : V → (analyticGerms V)ˣ) (r : V → ℕ) (T : Set V) :
    Ideal.span ((fun j => (u j : analyticGerms V) * coord j ^ r j) '' T) =
      truncGermIdealOn r T := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨j, hj, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, hj, rfl⟩)
  · rw [truncGermIdealOn, Ideal.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have e : coord j ^ r j = ↑(u j)⁻¹ * ((u j : analyticGerms V) * coord j ^ r j) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    change coord j ^ r j ∈ _
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, hj, rfl⟩)

/-- The ideal of a list of unit multiples of the powers w_j^{r_j}. -/
theorem ofList_map_unit_mul (u : V → (analyticGerms V)ˣ) (r : V → ℕ) (l : List V) :
    Ideal.ofList (l.map fun j => (u j : analyticGerms V) * coord j ^ r j) =
      truncGermIdealOn r {j | j ∈ l} := by
  rw [← span_image_unit_mul u]
  unfold Ideal.ofList
  congr 1
  ext x
  simp

/-- **Weakly regular sequence in ℂ{w}.** For a duplicate-free list of variables and units u_j,
the germs u_j w_j^{r_j} form a weakly regular sequence. -/
theorem isWeaklyRegular_unit_mul_coord_pow (u : V → (analyticGerms V)ˣ) (r : V → ℕ)
    {l : List V} (hl : l.Nodup) :
    RingTheory.Sequence.IsWeaklyRegular (analyticGerms V)
      (l.map fun j => (u j : analyticGerms V) * coord j ^ r j) := by
  classical
  refine ⟨fun i hi => ?_⟩
  have hi' : i < l.length := by simpa using hi
  have hI : (Ideal.ofList ((l.map fun j => (u j : analyticGerms V) * coord j ^ r j).take i) • ⊤ :
      Submodule (analyticGerms V) (analyticGerms V)) = truncGermIdealOn r {j | j ∈ l.take i} := by
    rw [smul_eq_mul, Ideal.mul_top, ← List.map_take, ofList_map_unit_mul]
  have hnot : l[i] ∉ {j | j ∈ l.take i} := by
    intro hmem
    have hdrop : l[i] ∈ l.drop i := by
      rw [List.drop_eq_getElem_cons hi']
      exact List.mem_cons_self
    exact List.disjoint_take_drop hl le_rfl hmem hdrop
  rw [hI, List.getElem_map, isSMulRegular_iff_right_eq_zero_of_smul]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul] at hx
  rw [Submodule.Quotient.mk_eq_zero]
  have h2 : coord l[i] ^ r l[i] * ((u l[i] : analyticGerms V) * f) ∈
      truncGermIdealOn r {j | j ∈ l.take i} := by
    rwa [mul_left_comm, ← mul_assoc]
  have h3 := mem_truncGermIdealOn_of_coord_pow_mul_mem hnot _ h2
  have e : f = ↑(u l[i])⁻¹ * ((u l[i] : analyticGerms V) * f) := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [e]
  exact Ideal.mul_mem_left _ _ h3

/-- The germ truncation ideal is proper when every r_i is positive: it lies in the kernel of the
value at 0. -/
theorem truncGermIdealOn_le_ker_evalZero {r : V → ℕ} (hr : ∀ i, 0 < r i) (T : Set V) :
    truncGermIdealOn r T ≤ RingHom.ker (evalZero : analyticGerms V →ₐ[ℂ] ℂ) := by
  rw [truncGermIdealOn, Ideal.span_le]
  rintro _ ⟨j, -, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, map_pow, evalZero_coord, zero_pow (hr j).ne']

/-- **Regular sequence in ℂ{w} (complete intersection).** If every r_i is positive, the germs
u_j w_j^{r_j}, each variable listed once, form a regular sequence in ℂ{w}. -/
theorem isRegular_unit_mul_coord_pow (u : V → (analyticGerms V)ˣ) {r : V → ℕ}
    (hr : ∀ i, 0 < r i) {l : List V} (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (analyticGerms V)
      (l.map fun j => (u j : analyticGerms V) * coord j ^ r j) := by
  refine ⟨isWeaklyRegular_unit_mul_coord_pow u r hl, ?_⟩
  rw [smul_eq_mul, Ideal.mul_top, ofList_map_unit_mul, ne_comm, Ne, Ideal.eq_top_iff_one]
  intro h1
  have h := truncGermIdealOn_le_ker_evalZero hr _ h1
  rw [RingHom.mem_ker, map_one] at h
  exact one_ne_zero h

/-- With all variables listed once, the sequence generates the truncation ideal. -/
theorem ofList_toList_map_coord_pow (r : V → ℕ) :
    Ideal.ofList ((Finset.univ : Finset V).toList.map fun j => coord j ^ r j) =
      truncGermIdeal r := by
  have h := ofList_map_unit_mul (fun _ => 1) r (Finset.univ : Finset V).toList
  simp only [Units.val_one, one_mul] at h
  rw [h, ← truncGermIdealOn_univ]
  congr 1
  ext j
  simp

/-- **Complete intersection.** If every r_i is positive, the powers w_i^{r_i}, each variable
listed once, form a regular sequence in ℂ{w} generating the truncation ideal
(`ofList_toList_map_coord_pow`). -/
theorem isRegular_toList_map_coord_pow {r : V → ℕ} (hr : ∀ i, 0 < r i) :
    RingTheory.Sequence.IsRegular (analyticGerms V)
      ((Finset.univ : Finset V).toList.map fun j => coord j ^ r j) := by
  have h := isRegular_unit_mul_coord_pow (fun _ => 1) hr (Finset.nodup_toList Finset.univ)
  simpa only [Units.val_one, one_mul] using h

end Regular

end BoundaryAlgebra

end BPFixedPoints
