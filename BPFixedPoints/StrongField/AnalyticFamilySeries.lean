import BPFixedPoints.StrongField.AnalyticDivision

/-!
# Multi-index power series and regrouping by exponent residues

This file supplies the power-series input for the free monomial basis of ℂ{w} over the convergent
parameter ring ℂ{p} of the state chart (supplement, `supp:boundary-algebra`), which is assembled
in `StrongField/AnalyticFamily.lean`. Multi-indices are functions β : V → ℕ, with total degree
`multiDeg β` = |β| and monomial function `monoFun β w` = w^β = ∏_j w_j^{β_j}.

* **Multi-index series are analytic** (`GeomBounded.hasFPowerSeriesAt`, `GeomBounded.analyticAt`):
  if ‖a_β‖ ≤ C K^{|β|} (`GeomBounded a`), then ∑_β a_β w^β converges near 0
  (`GeomBounded.eventually_hasSum`) to `mvSum a w`, and `mvSum a` has at 0 the formal multilinear
  series `mvSeries a`, whose n-th term is ∑_{|β| = n} a_β · w^β. The multilinear monomials come
  from words σ : Fin n → V (`wordMap`, `monoMap`, `exists_wcount_eq`); the radius is positive
  because there are at most 2^{|V| n} multi-indices of degree n (`card_multiDegSet_le`).
* **Uniqueness of coefficients** (`GeomBounded.eq_zero_of_eventuallyEq_zero`): if such a series
  vanishes near 0, every a_β vanishes, by uniqueness of power series on the diagonal
  (`HasFPowerSeriesAt.apply_eq_zero`) and of polynomial functions (`MvPolynomial.funext`).
* **Multi-index Taylor expansion** (`exists_geomBounded_hasSum`): a function analytic at 0 is near
  0 the sum of such a series. The coefficient of w^β sums the values of the |β|-th multilinear
  term on the standard basis vectors along the words with letter count β (`wordCoeff`,
  `apply_diag_eq_sum_wordCoeff`); it is bounded by |V|^{|β|} times the norm of that term.
* **Regrouping by exponent residues.** For r_i > 0, (α, γ) ↦ α + rγ identifies box × ℕ^V with ℕ^V
  (`boxProdEquiv`; the box is `truncBox r`). For c_i ≠ 0 and Ψ(w) = (c_i w_i^{r_i})_i
  (`scaledPowMap`), ∑_β a_β w^β = ∑_{α ∈ box} w^α g_α(Ψ(w)), where g_α has the coefficients
  a_{α+rγ} c^{−γ} (`residueCoeff`, `geomBounded_residueCoeff`,
  `GeomBounded.eventually_hasSum_regroup`). Conversely every family of coefficient series
  arises this way (`assembleCoeff`, `residueCoeff_assembleCoeff`).
* **The residue decomposition.** Existence (`exists_eventuallyEq_sum_monoFun_mul`): every f
  analytic at 0 is near 0 of the form f(w) = ∑_{α ∈ box} w^α g_α(Ψ(w)) with every g_α analytic at
  0. Uniqueness (`eventuallyEq_zero_of_sum_monoFun_mul`): if such a sum with g_α analytic at 0
  vanishes near 0, then every g_α vanishes near 0.

Not covered: Weierstrass division or preparation, convergent power series as an abstract ring,
and Cauchy estimates. The only analytic input is Mathlib's `HasFPowerSeriesOnBall`.
-/

set_option linter.unusedSectionVars false

open Filter Topology

namespace BPFixedPoints

namespace BoundaryAlgebra

section MultiIndex

variable {V : Type*} [Fintype V]

/-- The total degree |β| = ∑_j β_j of a multi-index β : V → ℕ. -/
def multiDeg (β : V → ℕ) : ℕ := ∑ j, β j

/-- The monomial function w ↦ w^β = ∏_j w_j^{β_j}. -/
def monoFun (β : V → ℕ) (w : V → ℂ) : ℂ := ∏ j, w j ^ β j

/-- w^{β+γ} = w^β w^γ. -/
theorem monoFun_add (β γ : V → ℕ) (w : V → ℂ) : monoFun (β + γ) w = monoFun β w * monoFun γ w := by
  simp [monoFun, pow_add, Finset.prod_mul_distrib]

/-- |w^β| ≤ ‖w‖^{|β|} for the sup norm. -/
theorem norm_monoFun_le (β : V → ℕ) (w : V → ℂ) : ‖monoFun β w‖ ≤ ‖w‖ ^ multiDeg β := by
  rw [monoFun, norm_prod, multiDeg, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) fun j _ => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm w j) _

/-- **Geometric multi-index series converge.** For 0 ≤ x < 1, ∑_β x^{|β|} converges. -/
theorem summable_pow_multiDeg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable fun β : V → ℕ => x ^ multiDeg β := by
  classical
  refine summable_of_sum_le (c := ((1 - x)⁻¹) ^ Fintype.card V) (fun β => pow_nonneg hx0 _)
    fun u => ?_
  obtain ⟨N, hN⟩ : ∃ N, ∀ β ∈ u, ∀ j, β j < N := ⟨u.sup (fun β => ∑ j, β j) + 1, fun β hβ j => by
      have h1 : β j ≤ ∑ j, β j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have h2 : ∑ j, β j ≤ u.sup (fun β => ∑ j, β j) := Finset.le_sup (f := fun β => ∑ j, β j) hβ
      omega⟩
  have hsub : u ⊆ Fintype.piFinset fun _ : V => Finset.range N := fun β hβ =>
    Fintype.mem_piFinset.2 fun j => Finset.mem_range.2 (hN β hβ j)
  have hgeom : ∑ k ∈ Finset.range N, x ^ k ≤ (1 - x)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hx0 hx1]
    exact (summable_geometric_of_lt_one hx0 hx1).sum_le_tsum _ fun _ _ => pow_nonneg hx0 _
  calc ∑ β ∈ u, x ^ multiDeg β
        ≤ ∑ β ∈ Fintype.piFinset fun _ : V => Finset.range N, x ^ multiDeg β :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => pow_nonneg hx0 _
    _ = ∏ _j : V, ∑ k ∈ Finset.range N, x ^ k := by
        rw [Finset.prod_univ_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [multiDeg, Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ _j : V, (1 - x)⁻¹ :=
        Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun _ _ => pow_nonneg hx0 _)
          fun _ _ => hgeom
    _ = (1 - x)⁻¹ ^ Fintype.card V := by rw [Finset.prod_const, Finset.card_univ]

/-- A multi-index family with geometric growth: ‖a_β‖ ≤ C K^{|β|}. -/
def GeomBounded (a : (V → ℕ) → ℂ) : Prop :=
  ∃ C K : ℝ, 0 ≤ K ∧ ∀ β, ‖a β‖ ≤ C * K ^ multiDeg β

/-- The constant of a geometric bound is nonnegative. -/
theorem nonneg_of_geom_bound {a : (V → ℕ) → ℂ} {C K : ℝ} (ha : ∀ β, ‖a β‖ ≤ C * K ^ multiDeg β) :
    0 ≤ C := by
  have h := (norm_nonneg _).trans (ha 0)
  simpa [multiDeg] using h

/-- The sum ∑_β a_β w^β of a multi-index power series (as an unconditional sum; it is only
meaningful where the family is summable). -/
noncomputable def mvSum (a : (V → ℕ) → ℂ) (w : V → ℂ) : ℂ := ∑' β, a β * monoFun β w

/-- Near 0, K ‖w‖ < 1. -/
theorem eventually_mul_norm_lt_one (K : ℝ) : ∀ᶠ w in 𝓝 (0 : V → ℂ), K * ‖w‖ < 1 := by
  have h : Tendsto (fun w : V → ℂ => K * ‖w‖) (𝓝 0) (𝓝 (K * ‖(0 : V → ℂ)‖)) :=
    tendsto_const_nhds.mul (continuous_norm.tendsto 0)
  exact h.eventually (eventually_lt_nhds (by simp))

/-- A family with geometric growth gives a summable series where K ‖w‖ < 1. -/
theorem summable_mul_monoFun {a : (V → ℕ) → ℂ} {C K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ β, ‖a β‖ ≤ C * K ^ multiDeg β) {w : V → ℂ} (hw : K * ‖w‖ < 1) :
    Summable fun β => a β * monoFun β w := by
  have hC := nonneg_of_geom_bound ha
  refine Summable.of_norm_bounded ((summable_pow_multiDeg (by positivity) hw).mul_left C)
    fun β => ?_
  rw [norm_mul, mul_pow]
  calc ‖a β‖ * ‖monoFun β w‖ ≤ (C * K ^ multiDeg β) * ‖w‖ ^ multiDeg β :=
        mul_le_mul (ha β) (norm_monoFun_le β w) (norm_nonneg _) (by positivity)
    _ = C * (K ^ multiDeg β * ‖w‖ ^ multiDeg β) := by ring

/-- **Convergence.** A family with geometric growth gives a summable series near 0. -/
theorem GeomBounded.eventually_summable {a : (V → ℕ) → ℂ} (ha : GeomBounded a) :
    ∀ᶠ w in 𝓝 (0 : V → ℂ), Summable fun β => a β * monoFun β w := by
  obtain ⟨C, K, hK, ha⟩ := ha
  filter_upwards [eventually_mul_norm_lt_one K] with w hw
  exact summable_mul_monoFun hK ha hw

/-- Near 0, the series converges to `mvSum a`. -/
theorem GeomBounded.eventually_hasSum {a : (V → ℕ) → ℂ} (ha : GeomBounded a) :
    ∀ᶠ w in 𝓝 (0 : V → ℂ), HasSum (fun β => a β * monoFun β w) (mvSum a w) := by
  filter_upwards [ha.eventually_summable] with w hw
  exact hw.hasSum

variable [DecidableEq V]

/-- The multi-indices of total degree n. -/
noncomputable def multiDegSet (n : ℕ) : Finset (V → ℕ) := Finset.univ.piAntidiag n

/-- Membership in `multiDegSet n`. -/
theorem mem_multiDegSet {n : ℕ} {β : V → ℕ} : β ∈ multiDegSet n ↔ multiDeg β = n := by
  simp [multiDegSet, multiDeg]

/-- **Grouping by degree.** A summable multi-index family is the sum of its homogeneous parts. -/
theorem hasSum_multiDegSet {b : (V → ℕ) → ℂ} (hb : Summable b) :
    HasSum (fun n => ∑ β ∈ multiDegSet n, b β) (∑' β, b β) := by
  have h := hb.hasSum.tsum_fiberwise multiDeg
  have e : (fun n => ∑ β ∈ multiDegSet n, b β) =
      fun n => ∑' β : (multiDeg ⁻¹' {n} : Set (V → ℕ)), b β.1 := by
    funext n
    have hs : (multiDeg ⁻¹' {n} : Set (V → ℕ)) = ↑(multiDegSet n : Finset (V → ℕ)) := by
      ext β
      simp [mem_multiDegSet]
    rw [hs, Finset.tsum_subtype']
  rw [e]
  exact h

/-- There are at most 2^{|V| n} multi-indices of degree n. -/
theorem card_multiDegSet_le (n : ℕ) :
    ((multiDegSet n : Finset (V → ℕ)).card : ℝ) ≤ 2 ^ (Fintype.card V * n) := by
  have hsub : (multiDegSet n : Finset (V → ℕ)) ⊆
      Fintype.piFinset fun _ : V => Finset.range (n + 1) :=
    fun β hβ => Fintype.mem_piFinset.2 fun j => Finset.mem_range.2 (by
      have h1 : β j ≤ ∑ j, β j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have h2 := mem_multiDegSet.1 hβ
      rw [multiDeg] at h2
      omega)
  have hc := Finset.card_le_card hsub
  rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_range, Finset.card_univ] at hc
  have h2 : (n + 1) ^ Fintype.card V ≤ 2 ^ (Fintype.card V * n) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (Nat.lt_two_pow_self) _
  exact_mod_cast hc.trans h2

/-- The number of occurrences of j in a word σ : Fin n → V. -/
def wcount {n : ℕ} (σ : Fin n → V) (j : V) : ℕ := (Finset.univ.filter fun k => σ k = j).card

/-- A word of length n has degree n. -/
theorem multiDeg_wcount {n : ℕ} (σ : Fin n → V) : multiDeg (wcount σ) = n := by
  unfold multiDeg wcount
  rw [← Finset.card_eq_sum_card_fiberwise (fun k _ => Finset.mem_coe.2 (Finset.mem_univ (σ k))),
    Finset.card_univ, Fintype.card_fin]

/-- The product of the letters of a word is the monomial of its letter counts. -/
theorem prod_word {n : ℕ} (σ : Fin n → V) (y : V → ℂ) : ∏ k, y (σ k) = monoFun (wcount σ) y := by
  rw [monoFun, ← Finset.prod_fiberwise Finset.univ σ (fun k => y (σ k))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_congr rfl (fun k hk => by rw [(Finset.mem_filter.1 hk).2]), Finset.prod_const,
    wcount]

/-- Every multi-index of degree n is the letter count of a word of length n. -/
theorem exists_wcount_eq {n : ℕ} {β : V → ℕ} (hβ : multiDeg β = n) :
    ∃ σ : Fin n → V, wcount σ = β := by
  subst hβ
  have hcard : Fintype.card (Σ j, Fin (β j)) = multiDeg β := by simp [multiDeg]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨fun k => (e.symm k).1, funext fun j => ?_⟩
  have h1 : (Finset.univ.filter fun k => (e.symm k).1 = j).card =
      (Finset.univ.filter fun x : Σ j, Fin (β j) => x.1 = j).card :=
    Finset.card_equiv e.symm (by simp)
  rw [wcount, h1, ← Fintype.card_subtype, Fintype.card_congr (Equiv.sigmaSubtype j),
    Fintype.card_fin]

/-- The multilinear monomial of a word: (m_0,…,m_{n−1}) ↦ ∏_k m_k(σ_k). -/
noncomputable def wordMap {n : ℕ} (σ : Fin n → V) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => V → ℂ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
    fun k => ContinuousLinearMap.proj (σ k)

/-- Values of the multilinear monomial. -/
theorem wordMap_apply {n : ℕ} (σ : Fin n → V) (m : Fin n → V → ℂ) :
    wordMap σ m = ∏ k, m k (σ k) := by
  simp [wordMap, ContinuousMultilinearMap.mkPiAlgebra_apply]

/-- The multilinear monomial has norm at most 1. -/
theorem norm_wordMap_le {n : ℕ} (σ : Fin n → V) : ‖wordMap σ‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun m => ?_
  rw [wordMap_apply, norm_prod, one_mul]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => norm_le_pi_norm (m k) (σ k)

/-- A continuous multilinear map whose diagonal is the monomial w^β, when |β| = n. -/
noncomputable def monoMap (n : ℕ) (β : V → ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => V → ℂ) ℂ :=
  if h : ∃ σ : Fin n → V, wcount σ = β then wordMap h.choose else 0

/-- On the diagonal, `monoMap n β` is the monomial w^β when |β| = n. -/
theorem monoMap_apply_diag {n : ℕ} {β : V → ℕ} (hβ : multiDeg β = n) (y : V → ℂ) :
    monoMap n β (fun _ => y) = monoFun β y := by
  have h : ∃ σ : Fin n → V, wcount σ = β := exists_wcount_eq hβ
  rw [monoMap, dite_eq_left h, wordMap_apply, prod_word, h.choose_spec]

/-- `monoMap n β` has norm at most 1. -/
theorem norm_monoMap_le (n : ℕ) (β : V → ℕ) : ‖monoMap n β‖ ≤ 1 := by
  unfold monoMap
  split_ifs
  · exact norm_wordMap_le _
  · simp

/-- The formal multilinear series of the multi-index power series ∑_β a_β w^β: its n-th term is
∑_{|β| = n} a_β · w^β. -/
noncomputable def mvSeries (a : (V → ℕ) → ℂ) : FormalMultilinearSeries ℂ (V → ℂ) ℂ :=
  fun n => ∑ β ∈ multiDegSet n, a β • monoMap n β

/-- The n-th term of `mvSeries a` on the diagonal. -/
theorem mvSeries_apply_diag (a : (V → ℕ) → ℂ) (n : ℕ) (y : V → ℂ) :
    mvSeries a n (fun _ => y) = ∑ β ∈ multiDegSet n, a β * monoFun β y := by
  simp only [mvSeries, sum_apply, smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun β hβ => by rw [monoMap_apply_diag (mem_multiDegSet.1 hβ)]

/-- Norm bound for the terms of `mvSeries`. -/
theorem norm_mvSeries_le {a : (V → ℕ) → ℂ} {C K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ β, ‖a β‖ ≤ C * K ^ multiDeg β) (n : ℕ) :
    ‖mvSeries a n‖ ≤ 2 ^ (Fintype.card V * n) * (C * K ^ n) := by
  have hC := nonneg_of_geom_bound ha
  calc ‖mvSeries a n‖ ≤ ∑ β ∈ multiDegSet n, ‖a β • monoMap n β‖ := norm_sum_le _ _
    _ ≤ ∑ _β ∈ multiDegSet n, C * K ^ n := Finset.sum_le_sum fun β hβ => by
        rw [norm_smul]
        calc ‖a β‖ * ‖monoMap n β‖ ≤ (C * K ^ n) * 1 :=
              mul_le_mul (by rw [← mem_multiDegSet.1 hβ]; exact ha β) (norm_monoMap_le n β)
                (norm_nonneg _) (by positivity)
          _ = C * K ^ n := mul_one _
    _ = (multiDegSet n : Finset (V → ℕ)).card * (C * K ^ n) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (card_multiDegSet_le n) (by positivity)

/-- `mvSeries a` has positive radius when a has geometric growth. -/
theorem radius_mvSeries_pos {a : (V → ℕ) → ℂ} {C K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ β, ‖a β‖ ≤ C * K ^ multiDeg β) : 0 < (mvSeries a).radius := by
  have hC := nonneg_of_geom_bound ha
  set d := Fintype.card V
  have hpos : (0 : ℝ) < 2 ^ d * (K + 1) := by positivity
  set t : NNReal := ⟨1 / (2 ^ d * (K + 1)), by positivity⟩ with ht_def
  have ht : (t : ℝ) = 1 / (2 ^ d * (K + 1)) := rfl
  have hKt : 2 ^ d * K * (t : ℝ) ≤ 1 := by
    rw [ht, mul_one_div, div_le_one hpos]
    nlinarith [pow_pos (two_pos (α := ℝ)) d]
  have hb : ∀ n, ‖mvSeries a n‖ * (t : ℝ) ^ n ≤ C := fun n => by
    calc ‖mvSeries a n‖ * (t : ℝ) ^ n ≤ 2 ^ (d * n) * (C * K ^ n) * (t : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (norm_mvSeries_le hK ha n) (by positivity)
      _ = C * (2 ^ d * K * t) ^ n := by rw [pow_mul, mul_pow, mul_pow]; ring
      _ ≤ C * 1 := by
          gcongr
          exact pow_le_one₀ (by positivity) hKt
      _ = C := mul_one C
  have htpos : (0 : ENNReal) < t := by
    rw [ENNReal.coe_pos, ← NNReal.coe_pos, ht]
    positivity
  exact htpos.trans_le ((mvSeries a).le_radius_of_bound C hb)

/-- **Analyticity of multi-index power series.** If a has geometric growth, `mvSum a` has the
power series `mvSeries a` at 0. -/
theorem GeomBounded.hasFPowerSeriesAt {a : (V → ℕ) → ℂ} (ha : GeomBounded a) :
    HasFPowerSeriesAt (mvSum a) (mvSeries a) 0 := by
  obtain ⟨C, K, hK, ha'⟩ := ha
  have hr := radius_mvSeries_pos hK ha'
  have h1 : HasFPowerSeriesAt (mvSeries a).sum (mvSeries a) 0 :=
    ((mvSeries a).hasFPowerSeriesOnBall hr).hasFPowerSeriesAt
  refine h1.congr ?_
  filter_upwards [eventually_mul_norm_lt_one K, Metric.eball_mem_nhds (0 : V → ℂ) hr]
    with w hw hw'
  have e1 := hasSum_multiDegSet (summable_mul_monoFun hK ha' hw)
  have e2 := (mvSeries a).hasSum hw'
  simp only [mvSeries_apply_diag] at e2
  exact e2.unique e1

omit [DecidableEq V] in
/-- **Analyticity of multi-index power series.** -/
theorem GeomBounded.analyticAt {a : (V → ℕ) → ℂ} (ha : GeomBounded a) :
    AnalyticAt ℂ (mvSum a) 0 := by
  classical
  exact ha.hasFPowerSeriesAt.analyticAt

omit [DecidableEq V] in
/-- **Uniqueness of coefficients.** If a has geometric growth and ∑_β a_β w^β vanishes near 0,
then every a_β vanishes. -/
theorem GeomBounded.eq_zero_of_eventuallyEq_zero {a : (V → ℕ) → ℂ} (ha : GeomBounded a)
    (h : mvSum a =ᶠ[𝓝 0] 0) (β₀ : V → ℕ) : a β₀ = 0 := by
  classical
  have hP : HasFPowerSeriesAt 0 (mvSeries a) 0 := ha.hasFPowerSeriesAt.congr h
  set n := multiDeg β₀
  have hz : ∀ y : V → ℂ, ∑ β ∈ multiDegSet n, a β * monoFun β y = 0 := fun y => by
    rw [← mvSeries_apply_diag]
    exact hP.apply_eq_zero n y
  let Q : MvPolynomial V ℂ :=
    ∑ β ∈ multiDegSet n, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm β) (a β)
  have hQ : Q = 0 := MvPolynomial.funext fun y => by
    rw [map_zero, ← hz y]
    simp only [Q, map_sum, MvPolynomial.eval_monomial]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), monoFun]
    simp
  have hc := congrArg (fun P : MvPolynomial V ℂ => P.coeff (Finsupp.equivFunOnFinite.symm β₀)) hQ
  simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    AddMonoidAlgebra.coeff_zero] at hc
  rw [Finset.sum_eq_single β₀] at hc
  · simpa using hc
  · intro β _ hβ
    exact ite_eq_right fun h' => hβ (Finsupp.equivFunOnFinite.symm.injective h')
  · intro hβ
    exact absurd (mem_multiDegSet.2 rfl) hβ

end MultiIndex

section Taylor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The j-th standard basis vector of ℂ^V. -/
def coordVec (j : V) : V → ℂ := fun i => if j = i then 1 else 0

/-- The standard basis vectors have norm at most 1. -/
theorem norm_coordVec_le (j : V) : ‖coordVec j‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
    unfold coordVec
    split_ifs <;> simp

/-- The coefficient of w^β in the homogeneous polynomial y ↦ q(y,…,y) of an n-linear map q: the
sum of q(e_{σ_0},…,e_{σ_{n−1}}) over the words σ with letter count β. -/
noncomputable def wordCoeff {n : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin n => V → ℂ) ℂ)
    (β : V → ℕ) : ℂ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : Fin n → V => wcount σ = β), q fun k => coordVec (σ k)

/-- **Expansion of a homogeneous term.** q(y,…,y) = ∑_{|β| = n} (coefficient) · y^β. -/
theorem apply_diag_eq_sum_wordCoeff {n : ℕ}
    (q : ContinuousMultilinearMap ℂ (fun _ : Fin n => V → ℂ) ℂ) (y : V → ℂ) :
    q (fun _ => y) = ∑ β ∈ multiDegSet n, wordCoeff q β * monoFun β y := by
  have hy : y = ∑ j, y j • coordVec j := pi_eq_sum_univ y
  have h1 : q (fun _ => y) = ∑ σ : Fin n → V, q fun k => y (σ k) • coordVec (σ k) := by
    conv_lhs => rw [hy]
    exact q.map_sum (fun _ j => y j • coordVec j)
  have h2 : ∀ σ : Fin n → V, (q fun k => y (σ k) • coordVec (σ k)) =
      (q fun k => coordVec (σ k)) * monoFun (wcount σ) y := fun σ => by
    rw [q.map_smul_univ, smul_eq_mul, prod_word, mul_comm]
  rw [h1, Finset.sum_congr rfl fun σ _ => h2 σ,
    ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := multiDegSet n) (g := wcount)
      (fun σ _ => mem_multiDegSet.2 (multiDeg_wcount σ))]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [wordCoeff, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ hσ => ?_
  rw [(Finset.mem_filter.1 hσ).2]

/-- The coefficients of q are bounded by |V|^n ‖q‖. -/
theorem norm_wordCoeff_le {n : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin n => V → ℂ) ℂ)
    (β : V → ℕ) : ‖wordCoeff q β‖ ≤ (Fintype.card V : ℝ) ^ n * ‖q‖ := by
  have hq : ∀ σ : Fin n → V, ‖q fun k => coordVec (σ k)‖ ≤ ‖q‖ := fun σ => by
    refine (q.le_opNorm _).trans ?_
    calc ‖q‖ * ∏ k, ‖coordVec (σ k)‖ ≤ ‖q‖ * 1 :=
          mul_le_mul_of_nonneg_left
            (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun k _ => norm_coordVec_le _)
            (norm_nonneg _)
      _ = ‖q‖ := mul_one _
  calc ‖wordCoeff q β‖
      ≤ ∑ σ ∈ Finset.univ.filter (fun σ : Fin n → V => wcount σ = β),
          ‖q fun k => coordVec (σ k)‖ := norm_sum_le _ _
    _ ≤ ∑ σ ∈ (Finset.univ : Finset (Fin n → V)), ‖q fun k => coordVec (σ k)‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => norm_nonneg _)
    _ ≤ ∑ _σ ∈ (Finset.univ : Finset (Fin n → V)), ‖q‖ := Finset.sum_le_sum fun σ _ => hq σ
    _ = (Fintype.card V : ℝ) ^ n * ‖q‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- The multi-index Taylor coefficients of a formal multilinear series on ℂ^V. -/
noncomputable def seriesCoeff (p : FormalMultilinearSeries ℂ (V → ℂ) ℂ) (β : V → ℕ) : ℂ :=
  wordCoeff (p (multiDeg β)) β

omit [DecidableEq V] in
/-- **Multi-index Taylor expansion.** A function analytic at 0 on ℂ^V is, near 0, the sum of a
multi-index power series ∑_β a_β w^β whose coefficients have geometric growth. -/
theorem exists_geomBounded_hasSum {f : (V → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ a : (V → ℕ) → ℂ, GeomBounded a ∧
      ∀ᶠ w in 𝓝 (0 : V → ℂ), HasSum (fun β => a β * monoFun β w) (f w) := by
  classical
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨t, ht0, htR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius (htR.trans_le hp.r_le)
  have ht : (0 : ℝ) < t := by exact_mod_cast ht0
  set K : ℝ := Fintype.card V / t with hK_def
  have hK : 0 ≤ K := by positivity
  have hbound : ∀ β, ‖seriesCoeff p β‖ ≤ C * K ^ multiDeg β := fun β => by
    have h1 := norm_wordCoeff_le (p (multiDeg β)) β
    have h2 := hC (multiDeg β)
    have e : (Fintype.card V : ℝ) ^ multiDeg β * ‖p (multiDeg β)‖ =
        K ^ multiDeg β * (‖p (multiDeg β)‖ * (t : ℝ) ^ multiDeg β) := by
      rw [hK_def, div_pow]
      field_simp
    calc ‖seriesCoeff p β‖ ≤ (Fintype.card V : ℝ) ^ multiDeg β * ‖p (multiDeg β)‖ := h1
      _ = K ^ multiDeg β * (‖p (multiDeg β)‖ * (t : ℝ) ^ multiDeg β) := e
      _ ≤ K ^ multiDeg β * C := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = C * K ^ multiDeg β := mul_comm _ _
  refine ⟨seriesCoeff p, ⟨C, K, hK, hbound⟩, ?_⟩
  filter_upwards [eventually_mul_norm_lt_one K, Metric.eball_mem_nhds (0 : V → ℂ) hp.r_pos]
    with w hw hwR
  have hs := summable_mul_monoFun hK hbound hw
  have e1 := hasSum_multiDegSet hs
  have e2 := hp.hasSum hwR
  rw [zero_add] at e2
  have e : (fun n => ∑ β ∈ multiDegSet n, seriesCoeff p β * monoFun β w) =
      fun n => p n fun _ => w := by
    funext n
    rw [apply_diag_eq_sum_wordCoeff]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [seriesCoeff, mem_multiDegSet.1 hβ]
  rw [e] at e1
  rw [e2.unique e1]
  exact hs.hasSum

end Taylor

section Regroup

variable {V : Type*} [Fintype V] {r : V → ℕ}

/-- The exponent box is a finite type. -/
noncomputable instance instFintypeTruncBox (r : V → ℕ) : Fintype (truncBox r) :=
  Fintype.ofFinite _

/-- The power map w ↦ (c_i w_i^{r_i})_i. -/
def scaledPowMap (r : V → ℕ) (c : V → ℂ) (w : V → ℂ) : V → ℂ := fun i => c i * w i ^ r i

/-- The power map is continuous. -/
theorem continuous_scaledPowMap (r : V → ℕ) (c : V → ℂ) : Continuous (scaledPowMap r c) :=
  continuous_pi fun i => continuous_const.mul ((continuous_apply i).pow _)

/-- For positive exponents the power map fixes 0. -/
theorem scaledPowMap_zero (hr : ∀ i, 0 < r i) (c : V → ℂ) : scaledPowMap r c 0 = 0 :=
  funext fun i => by simp [scaledPowMap, zero_pow (hr i).ne']

/-- For positive exponents the power map tends to 0 at 0. -/
theorem tendsto_scaledPowMap (hr : ∀ i, 0 < r i) (c : V → ℂ) :
    Tendsto (scaledPowMap r c) (𝓝 0) (𝓝 0) := by
  have h := (continuous_scaledPowMap r c).tendsto 0
  rwa [scaledPowMap_zero hr] at h

/-- **Exponent residues.** With all r_i > 0, (α, γ) ↦ α + r γ is a bijection from the box times
ℕ^V onto ℕ^V; its inverse is β ↦ (β mod r, β div r). -/
noncomputable def boxProdEquiv (hr : ∀ i, 0 < r i) : truncBox r × (V → ℕ) ≃ (V → ℕ) where
  toFun x i := (x.1 : V →₀ ℕ) i + r i * x.2 i
  invFun β := (⟨Finsupp.equivFunOnFinite.symm fun i => β i % r i, fun i => by
      simpa using Nat.mod_lt (β i) (hr i)⟩, fun i => β i / r i)
  left_inv x := by
    obtain ⟨⟨α, hα⟩, γ⟩ := x
    have hα' : ∀ i, α i < r i := hα
    refine Prod.ext (Subtype.ext (Finsupp.ext fun i => ?_)) (funext fun i => ?_)
    · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hα' i)]
    · simp [Nat.add_mul_div_left _ _ (hr i), Nat.div_eq_of_lt (hα' i)]
  right_inv β := funext fun i => by simp [Nat.mod_add_div]

/-- Values of `boxProdEquiv`. -/
theorem boxProdEquiv_apply (hr : ∀ i, 0 < r i) (α : truncBox r) (γ : V → ℕ) :
    boxProdEquiv hr (α, γ) = fun i => (α : V →₀ ℕ) i + r i * γ i := rfl

/-- **Regrouped coefficients.** For α in the box, b^α_γ = a_{α + rγ} c^{−γ}, so that
∑_γ a_{α+rγ} w^{α+rγ} = w^α ∑_γ b^α_γ (c w^r)^γ. -/
noncomputable def residueCoeff (hr : ∀ i, 0 < r i) (c : V → ℂ) (a : (V → ℕ) → ℂ)
    (α : truncBox r) (γ : V → ℕ) : ℂ :=
  a (boxProdEquiv hr (α, γ)) * ∏ i, (c i)⁻¹ ^ γ i

/-- w^{α + rγ} = w^α ∏_i (w_i^{r_i})^{γ_i}. -/
theorem monoFun_boxProdEquiv (hr : ∀ i, 0 < r i) (α : truncBox r) (γ : V → ℕ) (w : V → ℂ) :
    monoFun (boxProdEquiv hr (α, γ)) w = monoFun (α : V →₀ ℕ) w * ∏ i, (w i ^ r i) ^ γ i := by
  simp only [monoFun, boxProdEquiv_apply, pow_add, pow_mul, Finset.prod_mul_distrib]

/-- (c w^r)^γ = c^γ ∏_i (w_i^{r_i})^{γ_i}. -/
theorem monoFun_scaledPowMap (c : V → ℂ) (γ : V → ℕ) (w : V → ℂ) :
    monoFun γ (scaledPowMap r c w) = (∏ i, c i ^ γ i) * ∏ i, (w i ^ r i) ^ γ i := by
  simp only [monoFun, scaledPowMap, mul_pow, Finset.prod_mul_distrib]

/-- The term identity a_{α+rγ} w^{α+rγ} = w^α · b^α_γ (c w^r)^γ. -/
theorem mul_monoFun_boxProdEquiv (hr : ∀ i, 0 < r i) {c : V → ℂ} (hc : ∀ i, c i ≠ 0)
    (a : (V → ℕ) → ℂ) (α : truncBox r) (γ : V → ℕ) (w : V → ℂ) :
    a (boxProdEquiv hr (α, γ)) * monoFun (boxProdEquiv hr (α, γ)) w =
      monoFun (α : V →₀ ℕ) w * (residueCoeff hr c a α γ * monoFun γ (scaledPowMap r c w)) := by
  have hcc : (∏ i, (c i)⁻¹ ^ γ i) * ∏ i, c i ^ γ i = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => by rw [← mul_pow, inv_mul_cancel₀ (hc i), one_pow]
  rw [monoFun_boxProdEquiv, monoFun_scaledPowMap, residueCoeff]
  linear_combination (-(a (boxProdEquiv hr (α, γ)) * monoFun (α : V →₀ ℕ) w *
    ∏ i, (w i ^ r i) ^ γ i)) * hcc

/-- The regrouped coefficients inherit geometric growth. -/
theorem geomBounded_residueCoeff (hr : ∀ i, 0 < r i) (c : V → ℂ) {a : (V → ℕ) → ℂ}
    (ha : GeomBounded a) (α : truncBox r) : GeomBounded (residueCoeff hr c a α) := by
  obtain ⟨C, K, hK, ha⟩ := ha
  have hC := nonneg_of_geom_bound ha
  set M := ∑ i, K ^ r i * ‖(c i)⁻¹‖ with hM
  have hx : ∀ i, K ^ r i * ‖(c i)⁻¹‖ ≤ M := fun i =>
    Finset.single_le_sum (f := fun i => K ^ r i * ‖(c i)⁻¹‖) (fun i _ => by positivity)
      (Finset.mem_univ i)
  refine ⟨C * K ^ multiDeg ((α : V →₀ ℕ) : V → ℕ), M,
    Finset.sum_nonneg fun i _ => by positivity, fun γ => ?_⟩
  have hdeg : multiDeg (boxProdEquiv hr (α, γ)) =
      multiDeg ((α : V →₀ ℕ) : V → ℕ) + ∑ i, r i * γ i := by
    simp [multiDeg, boxProdEquiv_apply, Finset.sum_add_distrib]
  have hpow : K ^ multiDeg (boxProdEquiv hr (α, γ)) * ∏ i, ‖(c i)⁻¹‖ ^ γ i =
      K ^ multiDeg ((α : V →₀ ℕ) : V → ℕ) * ∏ i, (K ^ r i * ‖(c i)⁻¹‖) ^ γ i := by
    rw [hdeg, pow_add, ← Finset.prod_pow_eq_pow_sum, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_congr rfl fun i _ => by rw [mul_pow, pow_mul]
  rw [residueCoeff, norm_mul, norm_prod]
  simp only [norm_pow]
  calc ‖a (boxProdEquiv hr (α, γ))‖ * ∏ i, ‖(c i)⁻¹‖ ^ γ i
      ≤ C * K ^ multiDeg (boxProdEquiv hr (α, γ)) * ∏ i, ‖(c i)⁻¹‖ ^ γ i :=
        mul_le_mul_of_nonneg_right (ha _) (by positivity)
    _ = C * K ^ multiDeg ((α : V →₀ ℕ) : V → ℕ) * ∏ i, (K ^ r i * ‖(c i)⁻¹‖) ^ γ i := by
        rw [mul_assoc, hpow, mul_assoc]
    _ ≤ C * K ^ multiDeg ((α : V →₀ ℕ) : V → ℕ) * ∏ _i : V, M ^ γ _i := by
        gcongr with i
        exact hx i
    _ = C * K ^ multiDeg ((α : V →₀ ℕ) : V → ℕ) * M ^ multiDeg γ := by
        rw [Finset.prod_pow_eq_pow_sum]
        rfl

/-- **Regrouping by exponent residues.** If a has geometric growth, then near 0,
∑_β a_β w^β = ∑_{α ∈ box} w^α · g_α(c w^r), where g_α is the sum of the regrouped series
`residueCoeff`. -/
theorem GeomBounded.eventually_hasSum_regroup (hr : ∀ i, 0 < r i) {c : V → ℂ}
    (hc : ∀ i, c i ≠ 0) {a : (V → ℕ) → ℂ} (ha : GeomBounded a) :
    ∀ᶠ w in 𝓝 (0 : V → ℂ), HasSum (fun β => a β * monoFun β w)
      (∑ α : truncBox r,
        monoFun (α : V →₀ ℕ) w * mvSum (residueCoeff hr c a α) (scaledPowMap r c w)) := by
  have hres : ∀ᶠ w in 𝓝 (0 : V → ℂ), ∀ α : truncBox r,
      HasSum (fun γ => residueCoeff hr c a α γ * monoFun γ (scaledPowMap r c w))
        (mvSum (residueCoeff hr c a α) (scaledPowMap r c w)) :=
    Filter.eventually_all.2 fun α =>
      (tendsto_scaledPowMap hr c).eventually (geomBounded_residueCoeff hr c ha α).eventually_hasSum
  filter_upwards [ha.eventually_summable, hres] with w hw hres
  have h1 : HasSum ((fun β => a β * monoFun β w) ∘ boxProdEquiv hr) (∑' β, a β * monoFun β w) :=
    (boxProdEquiv hr).hasSum_iff.2 hw.hasSum
  have h2 : HasSum (fun α : truncBox r =>
      monoFun (α : V →₀ ℕ) w * mvSum (residueCoeff hr c a α) (scaledPowMap r c w))
      (∑' β, a β * monoFun β w) := by
    refine h1.prod_fiberwise fun α => ?_
    have h := (hres α).mul_left (monoFun (α : V →₀ ℕ) w)
    convert h using 2 with γ
    exact mul_monoFun_boxProdEquiv hr hc a α γ w
  rw [← h2.unique (hasSum_fintype _)]
  exact hw.hasSum

/-- **Assembling coefficients**, inverse to `residueCoeff`: a_{α+rγ} = b^α_γ c^γ. -/
noncomputable def assembleCoeff (hr : ∀ i, 0 < r i) (c : V → ℂ)
    (b : truncBox r → (V → ℕ) → ℂ) (β : V → ℕ) : ℂ :=
  b ((boxProdEquiv hr).symm β).1 ((boxProdEquiv hr).symm β).2 *
    ∏ i, c i ^ ((boxProdEquiv hr).symm β).2 i

/-- Regrouping the assembled coefficients returns them. -/
theorem residueCoeff_assembleCoeff (hr : ∀ i, 0 < r i) {c : V → ℂ} (hc : ∀ i, c i ≠ 0)
    (b : truncBox r → (V → ℕ) → ℂ) (α : truncBox r) :
    residueCoeff hr c (assembleCoeff hr c b) α = b α := by
  funext γ
  rw [residueCoeff, assembleCoeff, Equiv.symm_apply_apply, mul_assoc, ← Finset.prod_mul_distrib]
  have h : ∏ i, c i ^ γ i * (c i)⁻¹ ^ γ i = 1 :=
    Finset.prod_eq_one fun i _ => by rw [← mul_pow, mul_inv_cancel₀ (hc i), one_pow]
  rw [h, mul_one]

/-- Assembled coefficients have geometric growth if all the pieces do. -/
theorem geomBounded_assembleCoeff (hr : ∀ i, 0 < r i) (c : V → ℂ)
    {b : truncBox r → (V → ℕ) → ℂ} (hb : ∀ α, GeomBounded (b α)) :
    GeomBounded (assembleCoeff hr c b) := by
  choose C K hK hbound using hb
  have hC : ∀ α, 0 ≤ C α := fun α => nonneg_of_geom_bound (hbound α)
  set L := ∑ i, ‖c i‖ with hL_def
  have hL : 0 ≤ L := Finset.sum_nonneg fun i _ => norm_nonneg _
  set K' := 1 + L * ∑ α, K α with hK'_def
  have hK'1 : 1 ≤ K' := by
    have : 0 ≤ L * ∑ α, K α := mul_nonneg hL (Finset.sum_nonneg fun α _ => hK α)
    linarith
  refine ⟨∑ α, C α, K', by linarith, fun β => ?_⟩
  obtain ⟨⟨α, γ⟩, rfl⟩ := (boxProdEquiv hr).surjective β
  rw [assembleCoeff, Equiv.symm_apply_apply, norm_mul, norm_prod]
  simp only [norm_pow]
  have hγβ : multiDeg γ ≤ multiDeg (boxProdEquiv hr (α, γ)) := Finset.sum_le_sum fun i _ => by
    rw [boxProdEquiv_apply]
    have := hr i
    nlinarith
  have hcL : ∏ i, ‖c i‖ ^ γ i ≤ L ^ multiDeg γ := by
    rw [multiDeg, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ =>
      pow_le_pow_left₀ (norm_nonneg _)
        (Finset.single_le_sum (f := fun j => ‖c j‖) (fun j _ => norm_nonneg _)
          (Finset.mem_univ i)) _
  have hKL : K α * L ≤ K' := by
    have h1 : K α ≤ ∑ α, K α := Finset.single_le_sum (fun α _ => hK α) (Finset.mem_univ α)
    have h2 : K α * L ≤ L * ∑ α, K α := by nlinarith
    linarith
  have hCs : C α ≤ ∑ α, C α := Finset.single_le_sum (fun α _ => hC α) (Finset.mem_univ α)
  calc ‖b α γ‖ * ∏ i, ‖c i‖ ^ γ i ≤ (C α * K α ^ multiDeg γ) * L ^ multiDeg γ :=
        mul_le_mul (hbound α γ) hcL (by positivity)
          (mul_nonneg (hC α) (pow_nonneg (hK α) _))
    _ = C α * (K α * L) ^ multiDeg γ := by rw [mul_pow]; ring
    _ ≤ C α * K' ^ multiDeg γ :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (hK α) hL) hKL _) (hC α)
    _ ≤ C α * K' ^ multiDeg (boxProdEquiv hr (α, γ)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hK'1 hγβ) (hC α)
    _ ≤ (∑ α, C α) * K' ^ multiDeg (boxProdEquiv hr (α, γ)) :=
        mul_le_mul_of_nonneg_right hCs (pow_nonneg (by linarith) _)

/-- **Existence of the residue decomposition.** If every r_i > 0 and every c_i ≠ 0, a function f
analytic at 0 can be written near 0 as f(w) = ∑_{α ∈ box} w^α g_α(c w^r) with every g_α
analytic at 0. -/
theorem exists_eventuallyEq_sum_monoFun_mul (hr : ∀ i, 0 < r i) {c : V → ℂ} (hc : ∀ i, c i ≠ 0)
    {f : (V → ℂ) → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ g : truncBox r → (V → ℂ) → ℂ, (∀ α, AnalyticAt ℂ (g α) 0) ∧
      f =ᶠ[𝓝 0] fun w => ∑ α : truncBox r, monoFun (α : V →₀ ℕ) w * g α (scaledPowMap r c w) := by
  obtain ⟨a, ha, hfa⟩ := exists_geomBounded_hasSum hf
  refine ⟨fun α => mvSum (residueCoeff hr c a α),
    fun α => (geomBounded_residueCoeff hr c ha α).analyticAt,
    ?_⟩
  filter_upwards [hfa, ha.eventually_hasSum_regroup hr hc] with w h1 h2
  exact h1.unique h2

/-- **Uniqueness of the residue decomposition.** If every r_i > 0, every c_i ≠ 0, the g_α are
analytic at 0 and ∑_{α ∈ box} w^α g_α(c w^r) vanishes near 0, then every g_α vanishes near 0. -/
theorem eventuallyEq_zero_of_sum_monoFun_mul (hr : ∀ i, 0 < r i) {c : V → ℂ} (hc : ∀ i, c i ≠ 0)
    {g : truncBox r → (V → ℂ) → ℂ} (hg : ∀ α, AnalyticAt ℂ (g α) 0)
    (h : ∀ᶠ w in 𝓝 (0 : V → ℂ),
      ∑ α : truncBox r, monoFun (α : V →₀ ℕ) w * g α (scaledPowMap r c w) = 0)
    (α : truncBox r) : g α =ᶠ[𝓝 0] 0 := by
  choose b hb hgb using fun α => exists_geomBounded_hasSum (hg α)
  have hgb' : ∀ α, g α =ᶠ[𝓝 0] mvSum (b α) := fun α => by
    filter_upwards [hgb α, (hb α).eventually_hasSum] with q h1 h2
    exact h1.unique h2
  have ha := geomBounded_assembleCoeff hr c hb
  have hra := residueCoeff_assembleCoeff hr hc b
  have hall : ∀ᶠ w in 𝓝 (0 : V → ℂ), ∀ α : truncBox r,
      g α (scaledPowMap r c w) = mvSum (b α) (scaledPowMap r c w) :=
    Filter.eventually_all.2 fun α => (tendsto_scaledPowMap hr c).eventually (hgb' α)
  have hz : mvSum (assembleCoeff hr c b) =ᶠ[𝓝 0] 0 := by
    filter_upwards [ha.eventually_hasSum, ha.eventually_hasSum_regroup hr hc, hall, h]
      with w h1 h2 h3 h4
    rw [Pi.zero_apply, h1.unique h2, ← h4]
    exact Finset.sum_congr rfl fun α _ => by rw [hra, h3]
  have h0 := ha.eq_zero_of_eventuallyEq_zero hz
  have hb0 : b α = 0 := by
    rw [← hra α]
    funext γ
    simp [residueCoeff, h0]
  filter_upwards [hgb' α] with q hq
  rw [hq, hb0]
  simp [mvSum]

end Regroup

end BoundaryAlgebra

end BPFixedPoints
