import BPFixedPoints.Degree.Normalization

/-!
# The non-normalizable locus F ≡ −1: the edge chart

Fix a multigraph G (self-loops and parallel edges allowed) and parameters a : E → K, b : V → K
with a_e² ≠ 1 for every edge. The *non-normalizable locus* at (a,b) is the set of message vectors
y with

* `IsFixedPoint a b y` (the polynomial BP equations),
* nonzero messages and nonzero update denominators X_α + a_e, and
* F_i = −1 at every vertex (`IsNonnormalizableSolution`).

Equivalently y is a solution of the rational BP equations with nonzero messages and F ≡ −1
(`isNonnormalizableSolution_iff_rational`); no normalization condition 1 + F_i ≠ 0 is imposed.

Orient every edge as fst e → snd e and put x_e = y_{(e,false)}, the message from snd e to fst e.
On the locus the cavity ratios are X_α = −1/y_ᾱ and the update equation reads
y + x = a(1 + xy), i.e. y_{(e,true)} = h_{a_e}(x_e) with h_a(x) = (a − x)/(1 − a x)
(`edgeInvolution`). For a_e² ≠ 1 this file proves that y ↦ x is a bijection between the locus
and the *chart fiber*

  {x : E → K | x_e ≠ 0, x_e ≠ a_e, a_e x_e ≠ 1 for all e, and b_i Φ_i(a,x) = −1 for all i},

where Φ_i(a,x) = ∏_{fst e = i} x_e · ∏_{snd e = i} h_{a_e}(x_e) (`chartField`); the inverse is
`chartMessages` (`nonnormalizableChartEquiv`). This is the first paragraph of the proof of
`supp:nonnormalizable-dim`.

It also defines the Jacobian matrix ∂Φ_i/∂x_e of the chart equations (`chartJac`), proves that its
entries are the partial derivatives of Φ over any nontrivially normed field
(`hasDerivAt_chartField_update`), and calls a chart point *regular* when this Jacobian, as a map
K^E → K^V, is surjective (`IsRegularChartPoint`). Surjectivity is equivalent to the absence of a
nonzero row vector w with w·J = 0 (`isRegularChartPoint_iff`).

Nothing here is generic in (a,b); the generic statements are in the later
`NonnormalizableLocus*` files.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Chart

variable {K : Type*} [Field K]

/-- The edge involution h_a(x) = (a − x)/(1 − a x). -/
def edgeInvolution (a x : K) : K := (a - x) / (1 - a * x)

/-- The chart domain: x_e ≠ 0, x_e ≠ a_e and a_e x_e ≠ 1 for every edge. -/
def IsChartPoint (a x : E → K) : Prop := ∀ e, x e ≠ 0 ∧ x e ≠ a e ∧ a e * x e ≠ 1

/-- Chart messages: y_{(e,false)} = x_e and y_{(e,true)} = h_{a_e}(x_e). -/
def chartMessages (a x : E → K) (α : Dart E) : K :=
  if α.2 then edgeInvolution (a α.1) (x α.1) else x α.1

/-- Vertex product Φ_i(a,x) = ∏_{fst e = i} x_e · ∏_{snd e = i} h_{a_e}(x_e). -/
def chartField (a x : E → K) (i : V) : K :=
  ∏ e, (if G.fst e = i then x e else 1) * (if G.snd e = i then edgeInvolution (a e) (x e) else 1)

/-- The non-normalizable locus at (a,b): fixed points with nonzero messages, nonzero update
denominators and F_i = −1 at every vertex. -/
def IsNonnormalizableSolution (a : E → K) (b : V → K) (y : Dart E → K) : Prop :=
  G.IsFixedPoint a b y ∧ (∀ α, y α ≠ 0) ∧ (∀ α, G.cavity b y α + a α.1 ≠ 0) ∧
    ∀ i, G.totalField b y i = -1

/-- The chart fiber over (a,b): chart points with b_i Φ_i(a,x) = −1 at every vertex. -/
def IsChartSolution (a : E → K) (b : V → K) (x : E → K) : Prop :=
  IsChartPoint a x ∧ ∀ i, b i * G.chartField a x i = -1

/-- The locus written with the rational BP update: the update denominators are part of
`IsRationalFixedPoint`. -/
theorem isNonnormalizableSolution_iff_rational {a : E → K} {b : V → K} {y : Dart E → K} :
    G.IsNonnormalizableSolution a b y ↔
      G.IsRationalFixedPoint a b y ∧ (∀ α, y α ≠ 0) ∧ ∀ i, G.totalField b y i = -1 := by
  constructor
  · rintro ⟨hfix, hy, hden, hF⟩
    exact ⟨(G.isFixedPoint_iff_isRationalFixedPoint a b y hden).mp hfix, hy, hF⟩
  · rintro ⟨hrat, hy, hF⟩
    have hden : ∀ α, G.cavity b y α + a α.1 ≠ 0 := fun α => (hrat α).1
    exact ⟨(G.isFixedPoint_iff_isRationalFixedPoint a b y hden).mpr hrat, hy, hden, hF⟩

theorem one_sub_mul_ne_zero {a x : K} (h : a * x ≠ 1) : 1 - a * x ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm h)

theorem edgeInvolution_ne_zero {a x : K} (hxa : x ≠ a) (hax : a * x ≠ 1) :
    edgeInvolution a x ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr (Ne.symm hxa)) (one_sub_mul_ne_zero hax)

/-- a h_a(x) − 1 = (a² − 1)/(1 − a x). -/
theorem mul_edgeInvolution_sub_one {a x : K} (hax : a * x ≠ 1) :
    a * edgeInvolution a x - 1 = (a ^ 2 - 1) / (1 - a * x) := by
  have := one_sub_mul_ne_zero hax
  unfold edgeInvolution
  field_simp
  ring

theorem mul_edgeInvolution_ne_one {a x : K} (ha : a ^ 2 ≠ 1) (hax : a * x ≠ 1) :
    a * edgeInvolution a x ≠ 1 := by
  intro h
  have h' := mul_edgeInvolution_sub_one hax
  rw [h, sub_self] at h'
  exact ha (by
    have := (div_eq_zero_iff.mp h'.symm).resolve_right (one_sub_mul_ne_zero hax)
    linear_combination this)

/-- The edge relation h_a(x) + x = a(1 + x h_a(x)). -/
theorem edgeInvolution_add {a x : K} (hax : a * x ≠ 1) :
    edgeInvolution a x + x = a * (1 + x * edgeInvolution a x) := by
  have := one_sub_mul_ne_zero hax
  unfold edgeInvolution
  field_simp
  ring

/-- At a chart point every vertex product Φ_i is nonzero. -/
theorem chartField_ne_zero {a x : E → K} (hx : IsChartPoint a x) (i : V) :
    G.chartField a x i ≠ 0 := by
  rw [chartField, Finset.prod_ne_zero_iff]
  intro e _
  refine mul_ne_zero ?_ ?_
  · split_ifs
    · exact (hx e).1
    · exact one_ne_zero
  · split_ifs
    · exact edgeInvolution_ne_zero (hx e).2.1 (hx e).2.2
    · exact one_ne_zero

/-- The vertex product is the product of the chart messages entering i. -/
theorem prod_inDarts_chartMessages (a x : E → K) (i : V) :
    ∏ α ∈ G.inDarts i, chartMessages a x α = G.chartField a x i := by
  unfold inDarts chartField
  rw [Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [Fintype.prod_bool]
  simp only [head, chartMessages, Bool.cond_true, Bool.cond_false, ite_true]
  simp only [Bool.false_eq_true, ite_false]
  ring

theorem totalField_chartMessages (a x : E → K) (b : V → K) (i : V) :
    G.totalField b (chartMessages a x) i = b i * G.chartField a x i := by
  rw [totalField, prod_inDarts_chartMessages]

/-- On the locus F_{t(α)} = −1, the cavity ratio is X_α = −1/y_ᾱ. -/
theorem cavity_eq_of_totalField {b : V → K} {y : Dart E → K} (hy : ∀ α, y α ≠ 0)
    (hF : ∀ i, G.totalField b y i = -1) (α : Dart E) :
    G.cavity b y α = -1 / y (rev α) := by
  rw [eq_div_iff (hy _), ← G.totalField_tail_eq b y α, hF]

theorem cavity_add_eq_of_totalField {a : E → K} {b : V → K} {y : Dart E → K}
    (hy : ∀ α, y α ≠ 0) (hF : ∀ i, G.totalField b y i = -1) (α : Dart E) :
    G.cavity b y α + a α.1 = (a α.1 * y (rev α) - 1) / y (rev α) := by
  rw [G.cavity_eq_of_totalField hy hF α]
  field_simp [hy (rev α)]
  ring

theorem bpPoly_eq_of_totalField {a : E → K} {b : V → K} {y : Dart E → K}
    (hy : ∀ α, y α ≠ 0) (hF : ∀ i, G.totalField b y i = -1) (α : Dart E) :
    G.bpPoly a b y α =
      (a α.1 * (1 + y α * y (rev α)) - (y α + y (rev α))) / y (rev α) := by
  unfold bpPoly
  rw [G.cavity_eq_of_totalField hy hF α]
  field_simp [hy (rev α)]
  ring

/-- Chart points with b_i Φ_i = −1 give points of the non-normalizable locus. -/
theorem isNonnormalizableSolution_chartMessages {a x : E → K} {b : V → K}
    (ha : ∀ e, a e ^ 2 ≠ 1) (hx : G.IsChartSolution a b x) :
    G.IsNonnormalizableSolution a b (chartMessages a x) := by
  obtain ⟨hx, hb⟩ := hx
  have hy : ∀ α, chartMessages a x α ≠ 0 := by
    rintro ⟨e, _ | _⟩
    · exact (hx e).1
    · exact edgeInvolution_ne_zero (hx e).2.1 (hx e).2.2
  have hF : ∀ i, G.totalField b (chartMessages a x) i = -1 := fun i => by
    rw [totalField_chartMessages, hb]
  refine ⟨fun α => ?_, hy, fun α => ?_, hF⟩
  · rw [G.bpPoly_eq_of_totalField hy hF α]
    refine div_eq_zero_iff.mpr (Or.inl ?_)
    have h := edgeInvolution_add (hx α.1).2.2
    rcases α with ⟨e, _ | _⟩
    · simp only [rev, Bool.not_false, chartMessages, Bool.false_eq_true, ite_false, ite_true] at h ⊢
      linear_combination (-1 : K) * h
    · simp only [rev, Bool.not_true, chartMessages, Bool.false_eq_true, ite_false, ite_true] at h ⊢
      linear_combination (-1 : K) * h
  · rw [G.cavity_add_eq_of_totalField hy hF α]
    refine div_ne_zero (sub_ne_zero.mpr ?_) (hy _)
    rcases α with ⟨e, _ | _⟩
    · simp only [rev, Bool.not_false, chartMessages, ite_true]
      exact mul_edgeInvolution_ne_one (ha e) (hx e).2.2
    · simp only [rev, Bool.not_true, chartMessages, Bool.false_eq_true, ite_false]
      exact (hx e).2.2

/-- Points of the non-normalizable locus come from the chart: x_e = y_{(e,false)} is a chart
point, y_{(e,true)} = h_{a_e}(x_e), and b_i Φ_i(a,x) = −1. -/
theorem chart_of_isNonnormalizableSolution {a : E → K} {b : V → K} {y : Dart E → K}
    (hy : G.IsNonnormalizableSolution a b y) :
    y = chartMessages a (fun e => y (e, false)) ∧
      G.IsChartSolution a b (fun e => y (e, false)) := by
  obtain ⟨hfix, hy0, hden, hF⟩ := hy
  -- a x_e ≠ 1 from the update denominator of (e,true)
  have hax : ∀ e, a e * y (e, false) ≠ 1 := fun e => by
    have h := hden (e, true)
    rw [G.cavity_add_eq_of_totalField hy0 hF] at h
    simp only [rev, Bool.not_true] at h
    intro h1
    apply h
    rw [h1, sub_self, zero_div]
  have hrel : ∀ e, y (e, true) = edgeInvolution (a e) (y (e, false)) := fun e => by
    have h := hfix (e, true)
    rw [G.bpPoly_eq_of_totalField hy0 hF] at h
    simp only [rev, Bool.not_true] at h
    have h2 := (div_eq_zero_iff.mp h).resolve_right (hy0 _)
    have h3 := one_sub_mul_ne_zero (hax e)
    unfold edgeInvolution
    rw [eq_div_iff h3]
    linear_combination (-1 : K) * h2
  have hyeq : y = chartMessages a (fun e => y (e, false)) := by
    funext α
    rcases α with ⟨e, _ | _⟩
    · rfl
    · exact hrel e
  refine ⟨hyeq, fun e => ⟨hy0 _, fun h => ?_, hax e⟩, fun i => ?_⟩
  · apply hy0 (e, true)
    simp only at h
    rw [hrel e, h]
    unfold edgeInvolution
    rw [sub_self, zero_div]
  · rw [← totalField_chartMessages, ← hyeq, hF]

/-- **Edge chart of the non-normalizable locus.** For a_e² ≠ 1, y ↦ (y_{(e,false)})_e is a
bijection from the non-normalizable locus at (a,b) onto the chart fiber over (a,b); the inverse is
`chartMessages`. -/
def nonnormalizableChartEquiv {a : E → K} (b : V → K) (ha : ∀ e, a e ^ 2 ≠ 1) :
    {y // G.IsNonnormalizableSolution a b y} ≃ {x // G.IsChartSolution a b x} where
  toFun y := ⟨fun e => y.1 (e, false), (G.chart_of_isNonnormalizableSolution y.2).2⟩
  invFun x := ⟨chartMessages a x.1, G.isNonnormalizableSolution_chartMessages ha x.2⟩
  left_inv y := Subtype.ext (G.chart_of_isNonnormalizableSolution y.2).1.symm
  right_inv _ := Subtype.ext rfl

theorem nonnormalizable_nonempty_iff {a : E → K} (b : V → K) (ha : ∀ e, a e ^ 2 ≠ 1) :
    (∃ y, G.IsNonnormalizableSolution a b y) ↔ ∃ x, G.IsChartSolution a b x := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨_, ((G.nonnormalizableChartEquiv b ha) ⟨y, hy⟩).2⟩
  · rintro ⟨x, hx⟩
    exact ⟨_, ((G.nonnormalizableChartEquiv b ha).symm ⟨x, hx⟩).2⟩

end Chart

section Jacobian

variable {K : Type*} [Field K]

/-- Jacobian matrix of the chart equations, J_{i,e} = ∂Φ_i/∂x_e:
J_{i,e} = [fst e = i] Φ_i/x_e + [snd e = i] Φ_i (a_e² − 1)/((1 − a_e x_e)(a_e − x_e)). -/
def chartJac (a x : E → K) : Matrix V E K := fun i e =>
  (if G.fst e = i then G.chartField a x i / x e else 0) +
    (if G.snd e = i then
      G.chartField a x i * (a e ^ 2 - 1) / ((1 - a e * x e) * (a e - x e)) else 0)

/-- A chart point is regular when the Jacobian of the chart equations, as a map K^E → K^V, is
surjective (rank |V|). At a regular point of the chart fiber, the fiber is smooth of
dimension |E| − |V| by the Jacobian criterion. -/
def IsRegularChartPoint (a x : E → K) : Prop := Function.Surjective (G.chartJac a x).mulVec

omit [DecidableEq V] [DecidableEq E] in
/-- Over a field, a rectangular matrix has surjective `mulVec` iff `vecMul` has trivial kernel. -/
theorem surjective_mulVec_iff {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n K) :
    Function.Surjective M.mulVec ↔ ∀ w : m → K, Matrix.vecMul w M = 0 → w = 0 := by
  classical
  have h1 : Function.Surjective M.mulVec ↔ M.rank = Fintype.card m := by
    rw [Matrix.rank]
    constructor
    · intro hs
      rw [LinearMap.range_eq_top.mpr hs, finrank_top,
        Module.finrank_fintype_fun_eq_card]
    · intro h
      have := Submodule.eq_top_of_finrank_eq (h.trans (Module.finrank_fintype_fun_eq_card K).symm)
      exact LinearMap.range_eq_top.mp this
  have h2 : (∀ w : m → K, Matrix.vecMul w M = 0 → w = 0) ↔ M.transpose.rank = Fintype.card m := by
    have hrn := LinearMap.finrank_range_add_finrank_ker M.transpose.mulVecLin
    rw [Module.finrank_fintype_fun_eq_card] at hrn
    rw [Matrix.rank]
    have hk : (∀ w : m → K, Matrix.vecMul w M = 0 → w = 0) ↔
        LinearMap.ker M.transpose.mulVecLin = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      simp
    rw [hk, ← Submodule.finrank_eq_zero]
    omega
  rw [h1, h2, Matrix.rank_transpose]

/-- Regularity is the absence of a nonzero row vector w with w·J = 0. -/
theorem isRegularChartPoint_iff (a x : E → K) :
    G.IsRegularChartPoint a x ↔ ∀ w : V → K, Matrix.vecMul w (G.chartJac a x) = 0 → w = 0 :=
  surjective_mulVec_iff _

end Jacobian

section Derivative

variable {K : Type*} [NontriviallyNormedField K]

/-- The factor of Φ_i contributed by the edge e, as a function of a_e and x_e. -/
def chartFactor (i : V) (e : E) (a t : K) : K :=
  (if G.fst e = i then t else 1) * (if G.snd e = i then edgeInvolution a t else 1)

theorem chartField_update (a x : E → K) (i : V) (e : E) (t : K) :
    G.chartField a (Function.update x e t) i =
      G.chartFactor i e (a e) t * ∏ e' ∈ Finset.univ.erase e, G.chartFactor i e' (a e') (x e') := by
  change ∏ e', G.chartFactor i e' (a e') (Function.update x e t e') = _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ e)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun e' he' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase he')]

theorem hasDerivAt_edgeInvolution {a t : K} (h : a * t ≠ 1) :
    HasDerivAt (fun s => edgeInvolution a s) ((a ^ 2 - 1) / (1 - a * t) ^ 2) t := by
  have h1 : HasDerivAt (fun s => a - s) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub a
  have h2 : HasDerivAt (fun s => 1 - a * s) (-a) t := by
    simpa using ((hasDerivAt_id t).const_mul a).const_sub 1
  have := h1.div h2 (one_sub_mul_ne_zero h)
  convert this using 1
  · funext s
    rfl
  · ring

/-- **The Jacobian entries are partial derivatives.** At a chart point, t ↦ Φ_i(a, x[e ↦ t])
has derivative J_{i,e} at t = x_e. -/
theorem hasDerivAt_chartField_update (a x : E → K) (hx : IsChartPoint a x) (i : V) (e : E) :
    HasDerivAt (fun t => G.chartField a (Function.update x e t) i) (G.chartJac a x i e) (x e) := by
  set C := ∏ e' ∈ Finset.univ.erase e, G.chartFactor i e' (a e') (x e')
  have hfun : (fun t => G.chartField a (Function.update x e t) i) =
      fun t => G.chartFactor i e (a e) t * C := funext fun t => G.chartField_update a x i e t
  have hΦ : G.chartField a x i = G.chartFactor i e (a e) (x e) * C := by
    simpa using G.chartField_update a x i e (x e)
  rw [hfun]
  obtain ⟨hx0, hxa, hax⟩ := hx e
  have h1x := one_sub_mul_ne_zero hax
  have hax' : a e - x e ≠ 0 := sub_ne_zero.mpr (Ne.symm hxa)
  have hd := hasDerivAt_edgeInvolution hax
  unfold chartJac
  rw [hΦ]
  by_cases h1 : G.fst e = i <;> by_cases h2 : G.snd e = i
  · simp only [chartFactor, h1, h2, ite_true]
    refine (((hasDerivAt_id' (x e)).mul hd).mul_const C).congr_deriv ?_
    unfold edgeInvolution
    field_simp
  · simp only [chartFactor, h1, h2, ite_true, ite_false, mul_one, add_zero]
    refine ((hasDerivAt_id' (x e)).mul_const C).congr_deriv ?_
    field_simp
  · simp only [chartFactor, h1, h2, ite_true, ite_false, one_mul, zero_add]
    refine (hd.mul_const C).congr_deriv ?_
    unfold edgeInvolution
    field_simp
  · simp only [chartFactor, h1, h2, ite_false, one_mul, add_zero]
    exact hasDerivAt_const (x e) C

end Derivative

end Multigraph

end BPFixedPoints
