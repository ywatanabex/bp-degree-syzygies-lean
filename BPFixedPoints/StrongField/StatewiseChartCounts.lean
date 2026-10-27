import BPFixedPoints.StrongField.PowerMap
import BPFixedPoints.StrongField.Exhaustion
import BPFixedPoints.Real.Parity
import BPFixedPoints.Incidence.Generators

/-!
# Statewise strong-field chart counts (`sf:normal-form`, `fig:k4-states`, `real:all-real-states`)

For a state S (no vertex of S-degree one) and a power-map chart (Q,W,Φ) of
`StrongField/PowerMap.lean`, the chart solutions over p are the BP messages
y(π)=`chartY S π (Q π, W π)` at the roots π of p_i=(−1)^{k_i}π_i^{r_i} (`chartSols`).

**Complex counts.** Given a chart for every state, for all sufficiently small nonzero p the
chart of S contributes exactly wt(S)=∏_i φ(d_S(i)) admissible solutions at b=p⁻¹, charts of
different states are disjoint, and together they exhaust the Q(G) admissible solutions
(`exists_statewise_partition`). The proof combines `IsPowerMapChart.exists_card_solutions`,
`IsPowerMapChart.exists_chartY_ne`, Σ_{states} wt(S)=Q(G) (`sum_wt_states`) and the total count
`strong_field_exactly_Q_simple`: the disjoint union of the chart sets injects into a finite set
of the same cardinality. `exists_statewise_chart_counts` packages this with a choice of charts and
counts the chart solutions of any finite family of states (`card_chartSols_union`).

**Real counts.** The chart system, the chart messages and the power map commute with complex
conjugation (`chartMap_conj`, `chartY_conj`, `powerMap_conj`). If a, q⁰ and ω are real, the
uniqueness of the implicit-function branch gives Q(π̄)=conj Q(π) and W(π̄)=conj W(π) near π=0
(`IsPowerMapChart.eventually_conj`). Hence, for small real p>0, a chart solution is real iff its
chart coordinate π is real, and the real chart solutions are in bijection with the real roots of
the power map: exactly one if every k_i=d_S(i) is even (then every r_i is odd) and none otherwise
(then some r_i is even and π_i^{r_i}=−p_i<0) (`card_real_root`, `card_real_powerMap_roots`,
`IsPowerMapChart.exists_card_real`). For a_e>0 the units C_{S,i}(q⁰) are positive and ω can be
taken positive real (`exists_pos_rootTuple`), as in the proof of `real:strong-field-count`.
`exists_statewise_real_partition` and `exists_statewise_real_chart_counts` give Remark
`real:all-real-states` under its hypotheses a_e>0, a_e≠1 and small p_i>0: the chart of a state S
has exactly one real root if every d_S(i) is even and none otherwise; all its wt(S) roots are real
iff every d_S(i)∈{0,2} (the cycle unions indexing the module generators); the admissible real
solutions are exactly the real chart solutions, #{Eulerian S} in total. With ω positive, the real
chart root of S has π, Q(π), W(π) positive, hence messages positive off S and negative on S
(`IsPowerMapChart.exists_real_signs`); so it is the positive root iff S=∅, and the chart of S
is the sign sector `negSupport y = S` of `real_sign_sectors`. The remaining sentences of the
remark are `exists_four_le_deg_of_not_isCycleUnion` (an Eulerian state that is not a cycle union
has a vertex of degree ≥4 and wt(S)≥3) and `card_cycleUnions_eq_card_evenSets_iff` (the generator
states exhaust the Eulerian states iff every Eulerian set is a cycle union; the graph criterion
for this is `alg:generator-real-bridge`).

Only the positive orthant (small p_i>0, i.e. b_i→+∞) is treated here; the transport to the other
field orthants by the spin change `real:spin-gauge` is `StatewiseChartCountsOrthant.lean`.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

open Filter Topology

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section ChartSolutions

/-- Being a state is decidable (a finite conjunction over the vertices). -/
instance : DecidablePred (IsState G) := fun S => by unfold IsState; infer_instance

/-- The chart solutions of a power-map chart (Q,W) of the state S over the parameter p: the BP
message vectors y(π)=`chartY S π (Q π, W π)` at the roots π of the power map
p_i=(−1)^{k_i}π_i^{r_i}. -/
def chartSols (S : Finset E) (Q : (V → ℂ) → Dart E → ℂ) (W : (V → ℂ) → V → ℂ) (p : V → ℂ) :
    Set (Dart E → ℂ) :=
  {y | ∃ π, G.powerMap S π = p ∧ G.chartY S π (Sum.elim (Q π) (W π)) = y}

/-- Only states contribute to Q: Σ_{states S} wt(S) = Q(G). -/
theorem sum_wt_states : ∑ S ∈ Finset.univ.filter (IsState G), G.wt phi S = G.Q := by
  rw [Q, QOn, Finset.powerset_univ]
  refine Finset.sum_filter_of_ne fun S _ hS i hi => hS ?_
  rw [wt]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; rfl)

/-- ∏_i r_i = wt(S) for a state S. -/
theorem prod_rS_eq_wt_of_isState (S : Finset E) (hS : IsState G S) :
    ∏ i, G.rS S i = G.wt phi S := by
  rw [wt]
  exact Finset.prod_congr rfl fun i _ => G.rS_eq_phi S hS i

variable {G}
variable {a : E → ℂ} {ω : Finset E → V → ℂ} {Q : Finset E → (V → ℂ) → Dart E → ℂ}
  {W : Finset E → (V → ℂ) → V → ℂ} {Φ : Finset E → OpenPartialHomeomorph (V → ℂ) (V → ℂ)}

/-- **Statewise partition of the strong-field fiber.** Given a power-map chart for every state,
for all sufficiently small nonzero p: the chart of each state S contributes exactly wt(S)
solutions, every admissible solution at b=p⁻¹ lies in the chart of some state, the state is
unique, and every admissible solution is simple. -/
theorem exists_statewise_partition (hG : G.Loopless) (ha : ∀ e, a e ≠ 0)
    (ha1 : ∀ e, a e ^ 2 ≠ 1)
    (hc : ∀ S, IsState G S → G.IsPowerMapChart S a (ω S) (Q S) (W S) (Φ S)) :
    ∃ ε > 0, ∀ p : V → ℂ, (∀ i, p i ≠ 0) → (∀ i, ‖p i‖ < ε) →
      (∀ S, IsState G S → Nat.card (G.chartSols S (Q S) (W S) p) = G.wt phi S) ∧
      (∀ y, G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y ↔
        ∃ S, IsState G S ∧ y ∈ G.chartSols S (Q S) (W S) p) ∧
      (∀ S S' y, IsState G S → IsState G S' → y ∈ G.chartSols S (Q S) (W S) p →
        y ∈ G.chartSols S' (Q S') (W S') p → S = S') ∧
      (∀ y, G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y →
        G.IsSimpleSolution a (fun i => (p i)⁻¹) y) := by
  classical
  set St := {S : Finset E // IsState G S}
  have h1 := fun S : St => (hc S.1 S.2).exists_card_solutions S.2
  choose ε₁ hε₁ hcard₁ using h1
  have h2 : ∀ k : St × St, ∃ ε > 0, k.1.1 ≠ k.2.1 → ∀ p : V → ℂ, (∀ i, ‖p i‖ < ε) →
      ∀ π π', G.powerMap k.1.1 π = p → G.powerMap k.2.1 π' = p →
        G.chartY k.1.1 π (Sum.elim (Q k.1.1 π) (W k.1.1 π)) ≠
          G.chartY k.2.1 π' (Sum.elim (Q k.2.1 π') (W k.2.1 π')) := by
    intro k
    by_cases hk : k.1.1 = k.2.1
    · exact ⟨1, one_pos, fun h => absurd hk h⟩
    · obtain ⟨ε, hε, h⟩ := (hc _ k.1.2).exists_chartY_ne k.1.2 k.2.2 ha (hc _ k.2.2) hk
      exact ⟨ε, hε, fun _ => h⟩
  choose ε₂ hε₂ hne₂ using h2
  obtain ⟨ε₀, hε₀, h₀⟩ := strong_field_exactly_Q_simple hG ha ha1
  obtain ⟨δ₁, hδ₁, hδ₁le⟩ := exists_pos_forall_le ε₁ hε₁
  obtain ⟨δ₂, hδ₂, hδ₂le⟩ := exists_pos_forall_le ε₂ hε₂
  refine ⟨min ε₀ (min δ₁ δ₂), lt_min hε₀ (lt_min hδ₁ hδ₂), fun p hp hpε => ?_⟩
  have hp₀ : ∀ i, ‖p i‖ < ε₀ := fun i => (hpε i).trans_le (min_le_left _ _)
  have hp₁ : ∀ S : St, ∀ i, ‖p i‖ < ε₁ S := fun S i =>
    ((hpε i).trans_le ((min_le_right _ _).trans (min_le_left _ _))).trans_le (hδ₁le S)
  have hp₂ : ∀ k : St × St, ∀ i, ‖p i‖ < ε₂ k := fun k i =>
    ((hpε i).trans_le ((min_le_right _ _).trans (min_le_right _ _))).trans_le (hδ₂le k)
  obtain ⟨hQ, hsimple⟩ := h₀ p hp hp₀
  -- Per-state counts and admissibility.
  have hcard : ∀ S, IsState G S → Nat.card (G.chartSols S (Q S) (W S) p) = G.wt phi S := by
    intro S hS
    rw [← G.prod_rS_eq_wt_of_isState S hS]
    exact (hcard₁ ⟨S, hS⟩ p hp (hp₁ ⟨S, hS⟩)).1
  have hadm : ∀ S, IsState G S → ∀ y ∈ G.chartSols S (Q S) (W S) p,
      G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y := by
    rintro S hS y ⟨π, hπ, rfl⟩
    exact ((hcard₁ ⟨S, hS⟩ p hp (hp₁ ⟨S, hS⟩)).2 π hπ).1
  have huniq : ∀ S S' y, IsState G S → IsState G S' → y ∈ G.chartSols S (Q S) (W S) p →
      y ∈ G.chartSols S' (Q S') (W S') p → S = S' := by
    rintro S S' y hS hS' ⟨π, hπ, rfl⟩ ⟨π', hπ', hy⟩
    by_contra hSS
    exact hne₂ (⟨S, hS⟩, ⟨S', hS'⟩) hSS p (hp₂ _) π π' hπ hπ' hy.symm
  -- The disjoint union of the chart sets fills the fiber.
  set Sol := {y : Dart E → ℂ // G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y}
  have hfin : Finite Sol := Nat.finite_of_card_ne_zero (by rw [hQ]; exact G.Q_pos.ne')
  have hfinS : ∀ S : St, Finite (G.chartSols S.1 (Q S.1) (W S.1) p) := fun S =>
    Nat.finite_of_card_ne_zero (by
      rw [hcard S.1 S.2, ← G.prod_rS_eq_wt_of_isState S.1 S.2]
      exact Finset.prod_ne_zero_iff.2 fun i _ => (G.rS_pos S.1 S.2 i).ne')
  let f : (Σ S : St, G.chartSols S.1 (Q S.1) (W S.1) p) → Sol :=
    fun x => ⟨x.2.1, hadm x.1.1 x.1.2 x.2.1 x.2.2⟩
  have hf : Function.Injective f := by
    rintro ⟨S, y⟩ ⟨S', y'⟩ h
    have hy : y.1 = y'.1 := congrArg Subtype.val h
    have hSS : S = S' := Subtype.ext (huniq S.1 S'.1 y.1 S.2 S'.2 y.2 (hy ▸ y'.2))
    subst hSS
    have : y = y' := Subtype.ext hy
    subst this
    rfl
  have hcardSig : Nat.card (Σ S : St, G.chartSols S.1 (Q S.1) (W S.1) p) = G.Q := by
    rw [Nat.card_sigma, ← sum_wt_states]
    rw [Finset.sum_subtype (p := IsState G) (Finset.univ.filter (IsState G)) (fun S => by simp)
      (G.wt phi)]
    exact Finset.sum_congr rfl fun S _ => hcard S.1 S.2
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [hQ, hcardSig])
  refine ⟨hcard, fun y => ⟨fun hy => ?_, ?_⟩, huniq, hsimple⟩
  · obtain ⟨⟨S, y', hy'⟩, h⟩ := hbij.2 ⟨y, hy⟩
    have : y' = y := congrArg Subtype.val h
    exact ⟨S.1, S.2, this ▸ hy'⟩
  · rintro ⟨S, hS, hy⟩
    exact hadm S hS y hy

end ChartSolutions

section Conjugation

open ComplexConjugate

variable {S : Finset E}

/-- The chart system has real (integer) coefficients: it commutes with complex conjugation. -/
theorem chartMap_conj (x : E ⊕ V → ℂ) (z : Dart E ⊕ V → ℂ) :
    G.chartMap S (fun j => conj (x j), fun k => conj (z k)) =
      fun k => conj (G.chartMap S (x, z) k) := by
  funext k
  rcases k with α | i
  · simp only [chartMap, chartSys, chartEdge]
    split_ifs <;> simp [vA, vP, vQ, vW]
  · simp [chartMap, chartSys, chartVertex, vQ, vW, map_prod]

/-- The chart messages commute with complex conjugation. -/
theorem chartY_conj (π : V → ℂ) (z : Dart E ⊕ V → ℂ) :
    G.chartY S (fun i => conj (π i)) (fun k => conj (z k)) =
      fun α => conj (G.chartY S π z α) := by
  funext α
  simp only [chartY, chartF]
  split_ifs <;> simp

/-- The power map commutes with complex conjugation. -/
theorem powerMap_conj (π : V → ℂ) :
    G.powerMap S (fun i => conj (π i)) = fun i => conj (G.powerMap S π i) := by
  funext i
  simp [powerMap]

variable {G}
variable {a : E → ℂ} {ω : V → ℂ} {Q : (V → ℂ) → Dart E → ℂ} {W : (V → ℂ) → V → ℂ}
  {Φ : OpenPartialHomeomorph (V → ℂ) (V → ℂ)}

/-- **Conjugation symmetry of a real chart.** If a, q⁰ and ω are real, then near π=0 the chart
commutes with complex conjugation: Q(π̄)=conj Q(π) and W(π̄)=conj W(π). -/
theorem IsPowerMapChart.eventually_conj (hc : G.IsPowerMapChart S a ω Q W Φ)
    (ha : ∀ e, conj (a e) = a e) (hq : ∀ α, conj (G.q0 S a α) = G.q0 S a α)
    (hω : ∀ i, conj (ω i) = ω i) :
    ∀ᶠ π in 𝓝 (0 : V → ℂ), π ∈ Φ.source ∧ (fun i => conj (π i)) ∈ Φ.source ∧
      Q (fun i => conj (π i)) = (fun α => conj (Q π α)) ∧
      W (fun i => conj (π i)) = fun i => conj (W π i) := by
  set cj : (V → ℂ) → (V → ℂ) := fun π i => conj (π i)
  have hcj : Continuous cj :=
    continuous_pi fun i => Complex.continuous_conj.comp (continuous_apply i)
  have hcj0 : cj 0 = 0 := by funext i; simp [cj]
  have hsrc : ∀ᶠ π in 𝓝 (0 : V → ℂ), π ∈ Φ.source := Φ.open_source.mem_nhds hc.zero_mem
  have hsrc' : ∀ᶠ π in 𝓝 (0 : V → ℂ), cj π ∈ Φ.source :=
    hcj.continuousAt.preimage_mem_nhds (by rw [hcj0]; exact Φ.open_source.mem_nhds hc.zero_mem)
  set g : (V → ℂ) → (V → ℂ) × (Dart E ⊕ V → ℂ) :=
    fun π => (cj π, fun k => conj (Sum.elim (Q π) (W π) k))
  have hg : ContinuousAt g 0 := by
    refine hcj.continuousAt.prodMk (continuousAt_pi.2 fun k => ?_)
    rcases k with α | i
    · exact Complex.continuous_conj.continuousAt.comp
        ((continuous_apply α).continuousAt.comp (hc.analyticOnNhd_Q 0 hc.zero_mem).continuousAt)
    · exact Complex.continuous_conj.continuousAt.comp
        ((continuous_apply i).continuousAt.comp (hc.analyticOnNhd_W 0 hc.zero_mem).continuousAt)
  have hg0 : g 0 = ((0 : V → ℂ), Sum.elim (G.q0 S a) ω) := by
    refine Prod.ext hcj0 (funext fun k => ?_)
    rcases k with α | i
    · simp [g, hc.Q_zero, hq]
    · simp [g, hc.W_zero, hω]
  have hT : Tendsto g (𝓝 0) (𝓝 ((0 : V → ℂ), Sum.elim (G.q0 S a) ω)) := by
    rw [← hg0]; exact hg
  filter_upwards [hsrc, hsrc', hT.eventually hc.unique] with π h1 h2 h3
  have hsol : G.chartMap S (Sum.elim a (cj π), (g π).2) = 0 := by
    have h := G.chartMap_conj (S := S) (Sum.elim a π) (Sum.elim (Q π) (W π))
    have e : (fun j => conj (Sum.elim a π j)) = Sum.elim a (cj π) := by
      funext j; rcases j with e | i <;> simp [ha, cj]
    rw [e, hc.sol π h1] at h
    rw [h]
    funext k
    simp
  have h4 := h3 hsol
  refine ⟨h1, h2, funext fun α => ?_, funext fun i => ?_⟩
  · have := congrFun h4 (Sum.inl α)
    simp only [g, Sum.elim_inl] at this
    exact this.symm
  · have := congrFun h4 (Sum.inr i)
    simp only [g, Sum.elim_inr] at this
    exact this.symm

end Conjugation

section RealCount

open ComplexConjugate

variable {S : Finset E}

/-- For a state, an even degree k_i gives an odd exponent r_i (r_i=1 for k_i=0, k_i−1 otherwise). -/
theorem odd_rS_of_even (hS : IsState G S) {i : V} (he : Even (G.deg S i)) : Odd (G.rS S i) := by
  have hk := hS i
  unfold rS
  split_ifs with h0
  · exact odd_one
  · obtain ⟨m, hm⟩ := he
    exact ⟨m - 1, by omega⟩

/-- For a state, an odd degree k_i≥3 gives an even exponent r_i=k_i−1. -/
theorem even_rS_of_odd (hS : IsState G S) {i : V} (ho : Odd (G.deg S i)) : Even (G.rS S i) := by
  have hk := hS i
  unfold rS
  split_ifs with h0
  · rw [h0] at ho; exact absurd ho (by decide)
  · obtain ⟨m, hm⟩ := ho
    exact ⟨m, by omega⟩

/-- **Real roots of one power equation.** For a state S, a vertex i and c>0, the equation
x^{r_i}=(−1)^{k_i}c has exactly one real root if k_i=d_S(i) is even (then r_i is odd) and none
if k_i is odd (then r_i is even and (−1)^{k_i}c<0). -/
theorem card_real_root (hS : IsState G S) (i : V) {c : ℝ} (hc : 0 < c) :
    Nat.card {x : ℝ // x ^ G.rS S i = (-1) ^ G.deg S i * c} =
      if Even (G.deg S i) then 1 else 0 := by
  split_ifs with he
  · have hr := G.odd_rS_of_even hS he
    have hr0 : G.rS S i ≠ 0 := (G.rS_pos S hS i).ne'
    rw [he.neg_one_pow, one_mul, Nat.card_eq_one_iff_exists]
    refine ⟨⟨c ^ ((G.rS S i : ℝ)⁻¹), Real.rpow_inv_natCast_pow hc.le hr0⟩, fun x => ?_⟩
    exact Subtype.ext (hr.pow_injective (x.2.trans (Real.rpow_inv_natCast_pow hc.le hr0).symm))
  · have ho := Nat.not_even_iff_odd.1 he
    have hr := G.even_rS_of_odd hS ho
    rw [ho.neg_one_pow, Nat.card_eq_zero]
    left
    refine ⟨fun x => ?_⟩
    have h1 := x.2
    have h2 := hr.pow_nonneg x.1
    linarith

/-- A real root of x^{r_i}=(−1)^{k_i}c with c>0 is positive (and then k_i is even). -/
theorem pos_of_real_root (hS : IsState G S) {i : V} {c x : ℝ} (hc : 0 < c)
    (hx : x ^ G.rS S i = (-1) ^ G.deg S i * c) : 0 < x := by
  rcases Nat.even_or_odd (G.deg S i) with he | ho
  · rw [he.neg_one_pow, one_mul] at hx
    exact (G.odd_rS_of_even hS he).pow_pos_iff.1 (hx ▸ hc)
  · rw [ho.neg_one_pow] at hx
    have := (G.even_rS_of_odd hS ho).pow_nonneg x
    linarith

/-- **Real roots of the power map.** For a state S and p with all p_i>0, the power map
p_i=(−1)^{k_i}π_i^{r_i} has exactly one real root if S is Eulerian (every k_i even) and none
otherwise. -/
theorem card_real_powerMap_roots (hS : IsState G S) {p : V → ℝ} (hp : ∀ i, 0 < p i) :
    Nat.card {π : V → ℝ // ∀ i, π i ^ G.rS S i = (-1) ^ G.deg S i * p i} =
      if G.IsEvenSet S then 1 else 0 := by
  classical
  rw [Nat.card_congr (Equiv.subtypePiEquivPi
    (p := fun i (x : ℝ) => x ^ G.rS S i = (-1) ^ G.deg S i * p i)), Nat.card_pi]
  rw [Finset.prod_congr rfl fun i _ => G.card_real_root hS i (hp i), Finset.prod_boole]
  simp [IsEvenSet]

variable {G}
variable {ω : V → ℂ} {Q : (V → ℂ) → Dart E → ℂ} {W : (V → ℂ) → V → ℂ}
  {Φ : OpenPartialHomeomorph (V → ℂ) (V → ℂ)}

/-- **Real points of a real chart (`real:all-real-states`, `real:strong-field-count`).** Let a be
real, S a state and ω a real root tuple. For all sufficiently small real p>0, a chart solution of
S over p is real exactly when its chart coordinate π is real, so the real chart solutions are in
bijection with the real roots of p_i=(−1)^{k_i}π_i^{r_i}: there is exactly one if S is Eulerian
and none otherwise. -/
theorem IsPowerMapChart.exists_card_real (hS : IsState G S) {a : E → ℝ}
    (hc : G.IsPowerMapChart S (fun e => (a e : ℂ)) ω Q W Φ) (hω : ∀ i, conj (ω i) = ω i) :
    ∃ ε > 0, ∀ p : V → ℝ, (∀ i, 0 < p i) → (∀ i, p i < ε) →
      Nat.card {y : Dart E → ℝ //
          (fun α => (y α : ℂ)) ∈ G.chartSols S Q W (fun i => (p i : ℂ))} =
        if G.IsEvenSet S then 1 else 0 := by
  have haR : ∀ e, conj ((a e : ℂ)) = a e := fun e => Complex.conj_ofReal _
  have hqR : ∀ α, conj (G.q0 S (fun e => (a e : ℂ)) α) = G.q0 S (fun e => (a e : ℂ)) α := by
    intro α; unfold q0; split_ifs <;> simp
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hc.eventually_conj haR hqR hω)
  obtain ⟨ε, hε, hsmall⟩ := G.exists_norm_lt_of_powerMap hS hδ
  refine ⟨ε, hε, fun p hp hpε => ?_⟩
  set pC : V → ℂ := fun i => (p i : ℂ)
  have hpC : ∀ i, pC i ≠ 0 := fun i => by simp [pC, (hp i).ne']
  set Y : (V → ℂ) → Dart E → ℂ := fun π => G.chartY S π (Sum.elim (Q π) (W π))
  set cj : (V → ℂ) → (V → ℂ) := fun π i => conj (π i)
  have hnear : ∀ π, G.powerMap S π = pC →
      π ∈ Φ.source ∧ cj π ∈ Φ.source ∧ Y (cj π) = fun α => conj (Y π α) := by
    intro π hπ
    have hd : dist π 0 < δ := by
      rw [dist_zero_right]
      exact hsmall π fun i => by
        rw [hπ]
        simp only [pC, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hp i)]
        exact hpε i
    obtain ⟨h1, h2, hQc, hWc⟩ := hball hd
    refine ⟨h1, h2, ?_⟩
    have e : Sum.elim (Q (cj π)) (W (cj π)) = fun k => conj (Sum.elim (Q π) (W π) k) := by
      rw [hQc, hWc]
      funext k
      rcases k with α | i <;> rfl
    simp only [Y]
    rw [e, chartY_conj]
  have hcjpow : ∀ π, G.powerMap S π = pC → G.powerMap S (cj π) = pC := by
    intro π hπ
    rw [powerMap_conj, hπ]
    funext i
    simp [pC]
  have hnz : ∀ π, G.powerMap S π = pC → ∀ i, π i ≠ 0 := fun π hπ =>
    G.ne_zero_of_powerMap_eq hS hπ hpC
  have hpowR : ∀ πr : V → ℝ, (∀ i, πr i ^ G.rS S i = (-1) ^ G.deg S i * p i) ↔
      G.powerMap S (fun i => (πr i : ℂ)) = pC := by
    intro πr
    rw [powerMap_eq_iff]
    refine forall_congr' fun i => ?_
    simp only [pC]
    constructor <;> intro h <;> exact_mod_cast h
  -- At a real root, the chart messages are real.
  have hYreal : ∀ πr : V → ℝ, G.powerMap S (fun i => (πr i : ℂ)) = pC →
      ∀ α, ((Y (fun i => (πr i : ℂ)) α).re : ℂ) = Y (fun i => (πr i : ℂ)) α := by
    intro πr hπr α
    have hfix : cj (fun i => (πr i : ℂ)) = fun i => (πr i : ℂ) := by
      funext i; simp [cj]
    have h := congrFun (hnear _ hπr).2.2 α
    rw [hfix] at h
    exact Complex.conj_eq_iff_re.1 h.symm
  let f : {πr : V → ℝ // ∀ i, πr i ^ G.rS S i = (-1) ^ G.deg S i * p i} →
      {y : Dart E → ℝ // (fun α => (y α : ℂ)) ∈ G.chartSols S Q W pC} := fun πr =>
    ⟨fun α => (Y (fun i => (πr.1 i : ℂ)) α).re, fun i => (πr.1 i : ℂ), (hpowR πr.1).1 πr.2,
      funext fun α => (hYreal πr.1 ((hpowR πr.1).1 πr.2) α).symm⟩
  have hf : Function.Bijective f := by
    refine ⟨fun πr πr' h => ?_, fun y => ?_⟩
    · have h1 := (hpowR πr.1).1 πr.2
      have h2 := (hpowR πr'.1).1 πr'.2
      have hY : Y (fun i => (πr.1 i : ℂ)) = Y (fun i => (πr'.1 i : ℂ)) := by
        funext α
        have := congrArg (fun z => ((z.1 α : ℝ) : ℂ)) h
        simp only [f] at this
        rw [hYreal _ h1, hYreal _ h2] at this
        exact this
      have := hc.eq_of_chartY_eq (hnear _ h1).1 (hnear _ h2).1 (hnz _ h1) (hnz _ h2)
        (h1.trans h2.symm) hY
      exact Subtype.ext (funext fun i => Complex.ofReal_injective (congrFun this i))
    · obtain ⟨y, π, hπ, hy⟩ := y
      obtain ⟨h1, h2, h3⟩ := hnear π hπ
      have hY : Y (cj π) = Y π := by
        rw [h3]
        change (fun α => conj (Y π α)) = Y π
        rw [show Y π = fun α => (y α : ℂ) from hy]
        funext α
        exact Complex.conj_ofReal _
      have hcj : cj π = π := hc.eq_of_chartY_eq h2 h1 (hnz _ (hcjpow π hπ)) (hnz _ hπ)
        ((hcjpow π hπ).trans hπ.symm) hY
      have hπr : (fun i => ((π i).re : ℂ)) = π := funext fun i =>
        Complex.conj_eq_iff_re.1 (congrFun hcj i)
      refine ⟨⟨fun i => (π i).re, (hpowR _).2 (by rw [hπr]; exact hπ)⟩, Subtype.ext ?_⟩
      funext α
      simp only [f]
      rw [hπr]
      rw [show Y π = fun α => (y α : ℂ) from hy]
      exact Complex.ofReal_re _
  rw [← Nat.card_congr (Equiv.ofBijective f hf), G.card_real_powerMap_roots hS hp]

/-- **Signs of the real chart solutions (proof of `real:strong-field-count`).** Let a_e>0 and let
ω be a positive real root tuple. For all sufficiently small real p>0, every real chart solution y
of S over p is positive off S and negative on S: its coordinate π is real and positive, Q(π) and
W(π) are positive reals, so F_i>0, y_α=q_α>0 for α∉S and y_α=−F_{h(α)}/q_α<0 for α∈S. -/
theorem IsPowerMapChart.exists_real_signs (hS : IsState G S) {a : E → ℝ} (ha : ∀ e, 0 < a e)
    (hc : G.IsPowerMapChart S (fun e => (a e : ℂ)) ω Q W Φ)
    (hω : ∀ i, ∃ w : ℝ, 0 < w ∧ ω i = w) :
    ∃ ε > 0, ∀ p : V → ℝ, (∀ i, 0 < p i) → (∀ i, p i < ε) → ∀ y : Dart E → ℝ,
      (fun α => (y α : ℂ)) ∈ G.chartSols S Q W (fun i => (p i : ℂ)) →
        ∀ α, (α.1 ∉ S → 0 < y α) ∧ (α.1 ∈ S → y α < 0) := by
  have haR : ∀ e, conj ((a e : ℂ)) = a e := fun e => Complex.conj_ofReal _
  have hq : ∀ α, ∃ q : ℝ, 0 < q ∧ G.q0 S (fun e => (a e : ℂ)) α = q := by
    intro α
    unfold q0
    split_ifs
    · exact ⟨a α.1, ha _, rfl⟩
    · exact ⟨(a α.1)⁻¹, inv_pos.2 (ha _), by simp⟩
  have hqR : ∀ α, conj (G.q0 S (fun e => (a e : ℂ)) α) = G.q0 S (fun e => (a e : ℂ)) α := by
    intro α
    obtain ⟨q, -, hq'⟩ := hq α
    rw [hq']
    exact Complex.conj_ofReal q
  have hωR : ∀ i, conj (ω i) = ω i := by
    intro i
    obtain ⟨w, -, hw⟩ := hω i
    rw [hw]
    exact Complex.conj_ofReal w
  -- Near π=0 the real parts of Q and W stay positive.
  have hQpos : ∀ᶠ π in 𝓝 (0 : V → ℂ), ∀ α, 0 < (Q π α).re := by
    refine Filter.eventually_all.2 fun α => ?_
    have hcont : ContinuousAt (fun π => (Q π α).re) 0 :=
      Complex.continuous_re.continuousAt.comp ((continuous_apply α).continuousAt.comp
        (hc.analyticOnNhd_Q 0 hc.zero_mem).continuousAt)
    obtain ⟨q, hq0, hqe⟩ := hq α
    have h0 : 0 < (Q 0 α).re := by rw [hc.Q_zero, hqe, Complex.ofReal_re]; exact hq0
    exact hcont.eventually (lt_mem_nhds h0)
  have hWpos : ∀ᶠ π in 𝓝 (0 : V → ℂ), ∀ i, 0 < (W π i).re := by
    refine Filter.eventually_all.2 fun i => ?_
    have hcont : ContinuousAt (fun π => (W π i).re) 0 :=
      Complex.continuous_re.continuousAt.comp ((continuous_apply i).continuousAt.comp
        (hc.analyticOnNhd_W 0 hc.zero_mem).continuousAt)
    obtain ⟨w, hw0, hwe⟩ := hω i
    have h0 : 0 < (W 0 i).re := by rw [hc.W_zero, hwe, Complex.ofReal_re]; exact hw0
    exact hcont.eventually (lt_mem_nhds h0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    ((hc.eventually_conj haR hqR hωR).and (hQpos.and hWpos))
  obtain ⟨ε, hε, hsmall⟩ := G.exists_norm_lt_of_powerMap hS hδ
  refine ⟨ε, hε, fun p hp hpε y hy α => ?_⟩
  obtain ⟨π, hπ, hY⟩ := hy
  have hpC : ∀ i, ((p i : ℂ)) ≠ 0 := fun i => by simp [(hp i).ne']
  have hd : dist π 0 < δ := by
    rw [dist_zero_right]
    exact hsmall π fun i => by
      rw [hπ]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hp i)]
      exact hpε i
  obtain ⟨⟨h1, h2, hQc, hWc⟩, hQp, hWp⟩ := hball hd
  -- The coordinate π is real.
  have hpowc : G.powerMap S (fun i => conj (π i)) = fun i => (p i : ℂ) := by
    rw [powerMap_conj, hπ]
    funext i
    exact Complex.conj_ofReal _
  have hYc : G.chartY S (fun i => conj (π i))
      (Sum.elim (Q fun i => conj (π i)) (W fun i => conj (π i))) =
        G.chartY S π (Sum.elim (Q π) (W π)) := by
    have e : Sum.elim (Q fun i => conj (π i)) (W fun i => conj (π i)) =
        fun k => conj (Sum.elim (Q π) (W π) k) := by
      rw [hQc, hWc]
      funext k
      rcases k with α | i <;> rfl
    rw [e, chartY_conj, hY]
    funext α
    exact Complex.conj_ofReal _
  have hcj : (fun i => conj (π i)) = π :=
    hc.eq_of_chartY_eq h2 h1 (G.ne_zero_of_powerMap_eq hS hpowc hpC)
      (G.ne_zero_of_powerMap_eq hS hπ hpC) (hpowc.trans hπ.symm) hYc
  rw [hcj] at hQc hWc
  -- Real coordinates.
  obtain ⟨πr, hπr⟩ : ∃ πr : V → ℝ, ∀ i, π i = πr i :=
    ⟨fun i => (π i).re, fun i => (Complex.conj_eq_iff_re.1 (congrFun hcj i)).symm⟩
  obtain ⟨qr, hqr⟩ : ∃ qr : Dart E → ℝ, ∀ α, Q π α = qr α :=
    ⟨fun α => (Q π α).re, fun α => (Complex.conj_eq_iff_re.1 (congrFun hQc α).symm).symm⟩
  obtain ⟨wr, hwr⟩ : ∃ wr : V → ℝ, ∀ i, W π i = wr i :=
    ⟨fun i => (W π i).re, fun i => (Complex.conj_eq_iff_re.1 (congrFun hWc i).symm).symm⟩
  have hqpos : ∀ α, 0 < qr α := fun α => by
    have := hQp α
    rwa [hqr α, Complex.ofReal_re] at this
  have hwpos : ∀ i, 0 < wr i := fun i => by
    have := hWp i
    rwa [hwr i, Complex.ofReal_re] at this
  have hπpos : ∀ i, 0 < πr i := fun i => by
    have h := (G.powerMap_eq_iff π _).1 hπ i
    rw [hπr i] at h
    have h' : πr i ^ G.rS S i = (-1) ^ G.deg S i * p i := by exact_mod_cast h
    exact G.pos_of_real_root hS (hp i) h'
  have hyα : (y α : ℂ) = G.chartY S π (Sum.elim (Q π) (W π)) α := (congrFun hY α).symm
  simp only [chartY, chartF, Sum.elim_inl, Sum.elim_inr, hqr, hwr, hπr] at hyα
  have hf := mul_pos (hπpos (G.head α)) (hwpos (G.head α))
  refine ⟨fun hα => ?_, fun hα => ?_⟩
  · simp only [hα, ↓reduceIte] at hyα
    have : y α = qr α := by exact_mod_cast hyα
    rw [this]
    exact hqpos α
  · simp only [hα, ↓reduceIte] at hyα
    split_ifs at hyα
    · have : y α = -(πr (G.head α) * wr (G.head α))⁻¹ / qr α := by exact_mod_cast hyα
      rw [this]
      exact div_neg_of_neg_of_pos (neg_lt_zero.2 (inv_pos.2 hf)) (hqpos α)
    · have : y α = -(πr (G.head α) * wr (G.head α)) / qr α := by exact_mod_cast hyα
      rw [this]
      exact div_neg_of_neg_of_pos (neg_lt_zero.2 hf) (hqpos α)

end RealCount

section Assembly

open ComplexConjugate

/-- **Cardinality of a disjoint union.** If finitely many finite sets A_i (i∈T) are pairwise
disjoint with Nat.card (A_i)=c_i, their union has Σ_{i∈T} c_i elements. -/
theorem natCard_exists_mem_eq_sum {ι X : Type*} (T : Finset ι) (A : ι → Set X) (c : ι → ℕ)
    (hc : ∀ i ∈ T, Nat.card (A i) = c i) (hfin : ∀ i ∈ T, (A i).Finite)
    (hdisj : ∀ i ∈ T, ∀ j ∈ T, ∀ x, x ∈ A i → x ∈ A j → i = j) :
    Nat.card {x // ∃ i ∈ T, x ∈ A i} = ∑ i ∈ T, c i := by
  have : ∀ i : T, Finite (A i.1) := fun i => (hfin i.1 i.2).to_subtype
  let f : (Σ i : T, A i.1) → {x // ∃ i ∈ T, x ∈ A i} := fun x => ⟨x.2.1, x.1.1, x.1.2, x.2.2⟩
  have hf : Function.Bijective f := by
    refine ⟨?_, fun x => ?_⟩
    · rintro ⟨i, x⟩ ⟨j, x'⟩ h
      have hx : x.1 = x'.1 := congrArg Subtype.val h
      have hij : i = j := Subtype.ext (hdisj i.1 i.2 j.1 j.2 x.1 x.2 (hx ▸ x'.2))
      subst hij
      have : x = x' := Subtype.ext hx
      subst this
      rfl
    · obtain ⟨x, i, hi, hx⟩ := x
      exact ⟨⟨⟨i, hi⟩, x, hx⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_sigma, ← Finset.sum_coe_sort T c]
  exact Finset.sum_congr rfl fun i _ => hc i.1 i.2

variable {G}
variable {ω : Finset E → V → ℂ} {Q : Finset E → (V → ℂ) → Dart E → ℂ}
  {W : Finset E → (V → ℂ) → V → ℂ} {Φ : Finset E → OpenPartialHomeomorph (V → ℂ) (V → ℂ)}

/-- In the situation of `exists_statewise_partition`, the chart solutions of the states in a
finite family T number Σ_{states S∈T} wt(S). -/
theorem card_chartSols_union {p : V → ℂ}
    (hcard : ∀ S, IsState G S → Nat.card (G.chartSols S (Q S) (W S) p) = G.wt phi S)
    (huniq : ∀ S S' y, IsState G S → IsState G S' → y ∈ G.chartSols S (Q S) (W S) p →
      y ∈ G.chartSols S' (Q S') (W S') p → S = S') (T : Finset (Finset E)) :
    Nat.card {y // ∃ S ∈ T.filter (IsState G), y ∈ G.chartSols S (Q S) (W S) p} =
      ∑ S ∈ T.filter (IsState G), G.wt phi S := by
  refine natCard_exists_mem_eq_sum _ _ _ (fun S hS => hcard S (Finset.mem_filter.1 hS).2)
    (fun S hS => ?_) (fun S hS S' hS' y h h' =>
      huniq S S' y (Finset.mem_filter.1 hS).2 (Finset.mem_filter.1 hS').2 h h')
  have hS' := (Finset.mem_filter.1 hS).2
  refine Set.finite_coe_iff.1 (Nat.finite_of_card_ne_zero ?_)
  rw [hcard S hS', ← G.prod_rS_eq_wt_of_isState S hS']
  exact Finset.prod_ne_zero_iff.2 fun i _ => (G.rS_pos S hS' i).ne'

/-- **Statewise real counts for a family of real charts (`real:all-real-states`).** Let a_e>0,
a_e≠1 be real and take, for every state S, a power-map chart with a positive real root tuple
ω_S. For all sufficiently small real p>0, at b=p⁻¹:
* the chart of S contains exactly one real solution if S is Eulerian and none otherwise;
* all wt(S) chart solutions of S are real iff every d_S(i)∈{0,2} (S is a cycle union);
* the admissible real solutions are exactly the real chart solutions of the Eulerian states,
  each in the chart of exactly one state;
* with ω_S positive, a real chart solution of S is negative exactly on the edges of S, so it is
  positive iff S=∅, and a real admissible solution lies in the chart of a state S iff its
  negative-edge set is S;
* for every finite family T of edge sets the charts of the states in T contain #{Eulerian S∈T}
  real solutions. In particular there are #{Eulerian S} real solutions. -/
theorem exists_statewise_real_partition (hG : G.Loopless) {a : E → ℝ} (ha : ∀ e, 0 < a e)
    (ha1 : ∀ e, a e ≠ 1)
    (hc : ∀ S, IsState G S → G.IsPowerMapChart S (fun e => (a e : ℂ)) (ω S) (Q S) (W S) (Φ S))
    (hω : ∀ S, IsState G S → ∀ i, ∃ w : ℝ, 0 < w ∧ ω S i = w) :
    ∃ ε > 0, ∀ p : V → ℝ, (∀ i, 0 < p i) → (∀ i, p i < ε) →
      (∀ S, IsState G S → Nat.card {y : Dart E → ℝ //
          (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ))} =
        if G.IsEvenSet S then 1 else 0) ∧
      (∀ S, IsState G S → ((∀ y ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ)), ∀ α,
        (y α).im = 0) ↔ G.IsCycleUnion S)) ∧
      (∀ y : Dart E → ℝ, G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y ↔
        ∃ S, G.IsEvenSet S ∧
          (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ))) ∧
      (∀ S, IsState G S → ∀ y : Dart E → ℝ,
        (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ)) →
          negSupport y = S ∧ ((∀ α, 0 < y α) ↔ S = ∅)) ∧
      (∀ S, IsState G S → ∀ y : Dart E → ℝ, G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y →
        (negSupport y = S ↔
          (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ)))) ∧
      (∀ T : Finset (Finset E), Nat.card {y : Dart E → ℝ // ∃ S ∈ T.filter (IsState G),
          (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ))} =
        (T.filter G.IsEvenSet).card) ∧
      Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y} =
        (Finset.univ.filter G.IsEvenSet).card := by
  classical
  have haC : ∀ e, ((a e : ℂ)) ≠ 0 := fun e => by exact_mod_cast (ha e).ne'
  have haC1 : ∀ e, ((a e : ℂ)) ^ 2 ≠ 1 := by
    intro e h
    have h' : a e ^ 2 = 1 := by exact_mod_cast h
    have : (a e - 1) * (a e + 1) = 0 := by linear_combination h'
    rcases mul_eq_zero.1 this with h1 | h1
    · exact ha1 e (by linarith)
    · linarith [ha e]
  obtain ⟨ε₀, hε₀, h₀⟩ := exists_statewise_partition hG haC haC1 hc
  have hωR : ∀ S, IsState G S → ∀ i, conj (ω S i) = ω S i := fun S hS i => by
    obtain ⟨w, -, hwe⟩ := hω S hS i
    rw [hwe]
    exact Complex.conj_ofReal w
  have h1 := fun S : {S : Finset E // IsState G S} =>
    (hc S.1 S.2).exists_card_real S.2 (hωR S.1 S.2)
  choose ε₁ hε₁ hreal₁ using h1
  obtain ⟨δ₁, hδ₁, hδ₁le⟩ := exists_pos_forall_le ε₁ hε₁
  have h2 := fun S : {S : Finset E // IsState G S} =>
    (hc S.1 S.2).exists_real_signs S.2 ha (hω S.1 S.2)
  choose ε₂ hε₂ hsign₂ using h2
  obtain ⟨δ₂, hδ₂, hδ₂le⟩ := exists_pos_forall_le ε₂ hε₂
  refine ⟨min ε₀ (min δ₁ δ₂), lt_min hε₀ (lt_min hδ₁ hδ₂), fun p hp hpε => ?_⟩
  set pC : V → ℂ := fun i => (p i : ℂ)
  obtain ⟨hcard, hpart, huniq, -⟩ := h₀ pC (fun i => by simp [pC, (hp i).ne'])
    (fun i => by
      simp only [pC, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hp i)]
      exact (hpε i).trans_le (min_le_left _ _))
  have hreal : ∀ S, IsState G S → Nat.card {y : Dart E → ℝ //
      (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) pC} = if G.IsEvenSet S then 1 else 0 :=
    fun S hS => hreal₁ ⟨S, hS⟩ p hp fun i =>
      ((hpε i).trans_le ((min_le_right _ _).trans (min_le_left _ _))).trans_le
        (hδ₁le ⟨S, hS⟩)
  have hsign : ∀ S, IsState G S → ∀ y : Dart E → ℝ,
      (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) pC →
        ∀ α, (α.1 ∉ S → 0 < y α) ∧ (α.1 ∈ S → y α < 0) :=
    fun S hS => hsign₂ ⟨S, hS⟩ p hp fun i =>
      ((hpε i).trans_le ((min_le_right _ _).trans (min_le_right _ _))).trans_le
        (hδ₂le ⟨S, hS⟩)
  have hneg : ∀ S, IsState G S → ∀ y : Dart E → ℝ,
      (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) pC →
        negSupport y = S ∧ ((∀ α, 0 < y α) ↔ S = ∅) := by
    intro S hS y hy
    have h := hsign S hS y hy
    refine ⟨Finset.ext fun e => ?_, ⟨fun hpos => ?_, fun h0 α => ?_⟩⟩
    · simp only [negSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases he : e ∈ S
      · exact ⟨fun _ => he, fun _ => (h (e, true)).2 he⟩
      · exact ⟨fun hlt => absurd hlt (not_lt.2 ((h (e, true)).1 he).le), fun h' => absurd h' he⟩
    · refine Finset.eq_empty_of_forall_notMem fun e he => ?_
      exact absurd ((h (e, true)).2 he) (not_lt.2 (hpos (e, true)).le)
    · exact (h α).1 (by rw [h0]; exact Finset.notMem_empty _)
  have hfinC : ∀ S, IsState G S → Finite (G.chartSols S (Q S) (W S) pC) := fun S hS =>
    Nat.finite_of_card_ne_zero (by
      rw [hcard S hS, ← G.prod_rS_eq_wt_of_isState S hS]
      exact Finset.prod_ne_zero_iff.2 fun i _ => (G.rS_pos S hS i).ne')
  have hwt0 : ∀ S, IsState G S → G.wt phi S ≠ 0 := fun S hS => by
    rw [← G.prod_rS_eq_wt_of_isState S hS]
    exact Finset.prod_ne_zero_iff.2 fun i _ => (G.rS_pos S hS i).ne'
  -- Real messages as complex messages.
  set ι : (Dart E → ℝ) → Dart E → ℂ := fun y α => (y α : ℂ)
  have hι : Function.Injective ι := fun y y' h =>
    funext fun α => Complex.ofReal_injective (congrFun h α)
  -- All roots real iff cycle union.
  have hall : ∀ S, IsState G S → ((∀ y ∈ G.chartSols S (Q S) (W S) pC, ∀ α, (y α).im = 0) ↔
      G.IsCycleUnion S) := by
    intro S hS
    constructor
    · intro h
      have hbij : Function.Bijective (fun y : {y : Dart E → ℝ //
          ι y ∈ G.chartSols S (Q S) (W S) pC} =>
            (⟨ι y.1, y.2⟩ : G.chartSols S (Q S) (W S) pC)) := by
        refine ⟨fun y y' hy => Subtype.ext (hι (congrArg Subtype.val hy)), fun z => ?_⟩
        have hz : ι (fun α => (z.1 α).re) = z.1 := funext fun α =>
          Complex.conj_eq_iff_re.1 (Complex.conj_eq_iff_im.2 (h z.1 z.2 α))
        exact ⟨⟨fun α => (z.1 α).re, hz ▸ z.2⟩, Subtype.ext hz⟩
      have := Nat.card_congr (Equiv.ofBijective _ hbij)
      rw [hreal S hS, hcard S hS] at this
      rw [← G.wt_eq_one_iff]
      split_ifs at this
      · exact this.symm
      · exact absurd this.symm (hwt0 S hS)
    · intro hU
      have hE : G.IsEvenSet S := fun v => by
        rcases hU v with h | h <;> rw [h] <;> decide
      have h1 : Nat.card {y : Dart E → ℝ // ι y ∈ G.chartSols S (Q S) (W S) pC} = 1 := by
        rw [hreal S hS]; simp [hE]
      rw [Nat.card_eq_one_iff_exists] at h1
      obtain ⟨⟨y0, hy0⟩, -⟩ := h1
      have h2 := hcard S hS
      rw [(G.wt_eq_one_iff S).2 hU, Nat.card_eq_one_iff_unique] at h2
      intro z hz α
      have : z = ι y0 := congrArg Subtype.val (h2.1.elim ⟨z, hz⟩ ⟨ι y0, hy0⟩)
      rw [this]
      exact Complex.ofReal_im _
  -- Real chart solutions only occur for Eulerian states.
  have hfinR : ∀ S, IsState G S →
      Finite {y : Dart E → ℝ // ι y ∈ G.chartSols S (Q S) (W S) pC} := fun S hS => by
    have := hfinC S hS
    exact Finite.of_injective
      (fun y : {y : Dart E → ℝ // ι y ∈ G.chartSols S (Q S) (W S) pC} =>
        (⟨ι y.1, y.2⟩ : G.chartSols S (Q S) (W S) pC))
      fun y y' h => Subtype.ext (hι (congrArg Subtype.val h))
  have hEul : ∀ S, IsState G S → ∀ y : Dart E → ℝ, ι y ∈ G.chartSols S (Q S) (W S) pC →
      G.IsEvenSet S := by
    intro S hS y hy
    have := hfinR S hS
    have hpos : 0 < Nat.card {y : Dart E → ℝ // ι y ∈ G.chartSols S (Q S) (W S) pC} :=
      Nat.card_pos_iff.2 ⟨⟨⟨y, hy⟩⟩, inferInstance⟩
    rw [hreal S hS] at hpos
    by_contra hE
    simp [hE] at hpos
  -- Real admissible solutions are the real chart solutions.
  have hb : (Complex.ofRealHom ∘ fun i => (p i)⁻¹) = fun i => (pC i)⁻¹ := by
    funext i; simp [pC]
  have hrpart' : ∀ y : Dart E → ℝ, G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y ↔
      ∃ S, IsState G S ∧ ι y ∈ G.chartSols S (Q S) (W S) pC := by
    intro y
    rw [← G.isAdmissibleSolution_map_iff Complex.ofRealHom a (fun i => (p i)⁻¹) y, hb]
    exact hpart (ι y)
  have hrpart : ∀ y : Dart E → ℝ, G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y ↔
      ∃ S, G.IsEvenSet S ∧ ι y ∈ G.chartSols S (Q S) (W S) pC := by
    intro y
    rw [hrpart']
    constructor
    · rintro ⟨S, hS, hy⟩
      exact ⟨S, hEul S hS y hy, hy⟩
    · rintro ⟨S, hE, hy⟩
      exact ⟨S, G.isContributing_of_isEvenSet hE, hy⟩
  -- Real counts over families of states.
  have hT : ∀ T : Finset (Finset E), Nat.card {y : Dart E → ℝ // ∃ S ∈ T.filter (IsState G),
      ι y ∈ G.chartSols S (Q S) (W S) pC} = (T.filter G.IsEvenSet).card := by
    intro T
    have h := natCard_exists_mem_eq_sum (T.filter (IsState G))
      (fun S => {y : Dart E → ℝ | ι y ∈ G.chartSols S (Q S) (W S) pC})
      (fun S => if G.IsEvenSet S then 1 else 0)
      (fun S hS => hreal S (Finset.mem_filter.1 hS).2)
      (fun S hS => Set.finite_coe_iff.1 (hfinR S (Finset.mem_filter.1 hS).2))
      (fun S hS S' hS' y h h' =>
        huniq S S' (ι y) (Finset.mem_filter.1 hS).2 (Finset.mem_filter.1 hS').2 h h')
    rw [Finset.sum_boole, Finset.filter_filter] at h
    refine h.trans ?_
    simp only [Nat.cast_id]
    congr 1
    ext S
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, G.isContributing_of_isEvenSet h.2, h.2⟩⟩
  have hsector : ∀ S, IsState G S → ∀ y : Dart E → ℝ,
      G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y →
        (negSupport y = S ↔ (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) pC) := by
    intro S hS y hy
    obtain ⟨S', hS', hyS'⟩ := (hrpart y).1 hy
    have hS'n := (hneg S' (G.isContributing_of_isEvenSet hS') y hyS').1
    constructor
    · rintro rfl
      rw [hS'n]
      exact hyS'
    · intro hyS
      rw [hS'n]
      exact huniq S' S (ι y) (G.isContributing_of_isEvenSet hS') hS hyS' hyS
  refine ⟨hreal, hall, hrpart, hneg, hsector, hT, ?_⟩
  rw [← hT Finset.univ]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by
    rw [hrpart']
    simp)

variable (G)

/-- **Statewise complex chart counts (`sf:normal-form`, `sf:exhaustion`, `fig:k4-states`).** For
a loopless graph and fixed a_e≠0 with a_e²≠1 there are power-map charts, one for every state S,
such that for all sufficiently small nonzero p, at b=p⁻¹:
* the chart of S contributes exactly wt(S)=∏_i φ(d_S(i)) solutions;
* every admissible solution lies in the chart of exactly one state, so the charts partition the
  Q(G) admissible solutions, all of which are simple;
* for every finite family T of edge sets, the charts of the states in T contain
  Σ_{states S∈T} wt(S) solutions. -/
theorem exists_statewise_chart_counts (hG : G.Loopless) {a : E → ℂ} (ha : ∀ e, a e ≠ 0)
    (ha1 : ∀ e, a e ^ 2 ≠ 1) :
    ∃ (ω : Finset E → V → ℂ) (Q : Finset E → (V → ℂ) → Dart E → ℂ)
      (W : Finset E → (V → ℂ) → V → ℂ) (Φ : Finset E → OpenPartialHomeomorph (V → ℂ) (V → ℂ)),
      (∀ S, IsState G S → G.IsPowerMapChart S a (ω S) (Q S) (W S) (Φ S)) ∧
      ∃ ε > 0, ∀ p : V → ℂ, (∀ i, p i ≠ 0) → (∀ i, ‖p i‖ < ε) →
        (∀ S, IsState G S → Nat.card (G.chartSols S (Q S) (W S) p) = G.wt phi S) ∧
        (∀ y, G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y ↔
          ∃ S, IsState G S ∧ y ∈ G.chartSols S (Q S) (W S) p) ∧
        (∀ S S' y, IsState G S → IsState G S' → y ∈ G.chartSols S (Q S) (W S) p →
          y ∈ G.chartSols S' (Q S') (W S') p → S = S') ∧
        (∀ T : Finset (Finset E),
          Nat.card {y // ∃ S ∈ T.filter (IsState G), y ∈ G.chartSols S (Q S) (W S) p} =
            ∑ S ∈ T.filter (IsState G), G.wt phi S) ∧
        Nat.card {y // G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y} = G.Q ∧
        (∀ y, G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y →
          G.IsSimpleSolution a (fun i => (p i)⁻¹) y) := by
  classical
  have hex : ∀ S : Finset E, ∃ (ω : V → ℂ) (Q : (V → ℂ) → Dart E → ℂ) (W : (V → ℂ) → V → ℂ)
      (Φ : OpenPartialHomeomorph (V → ℂ) (V → ℂ)), IsState G S →
        G.IsPowerMapChart S a ω Q W Φ := by
    intro S
    by_cases hS : IsState G S
    · obtain ⟨ω, Q, W, Φ, hc, -⟩ := G.exists_powerMap_normal_form hG hS ha ha1
      exact ⟨ω, Q, W, Φ, fun _ => hc⟩
    · exact ⟨0, 0, 0, OpenPartialHomeomorph.refl _, fun h => absurd h hS⟩
  choose ω Q W Φ hc using hex
  obtain ⟨ε, hε, h⟩ := exists_statewise_partition hG ha ha1 hc
  refine ⟨ω, Q, W, Φ, hc, ε, hε, fun p hp hpε => ?_⟩
  obtain ⟨hcard, hpart, huniq, hsimple⟩ := h p hp hpε
  have hT := card_chartSols_union hcard huniq
  refine ⟨hcard, hpart, huniq, hT, ?_, hsimple⟩
  rw [← G.sum_wt_states, ← hT Finset.univ]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by rw [hpart]; simp)

/-- **Real root tuples (proof of `real:strong-field-count`).** For a_e>0 the base messages q⁰ are
positive reals, hence so is each unit C_{S,i}(q⁰), and it has a positive real r_i-th root. -/
theorem exists_pos_rootTuple {S : Finset E} (hS : IsState G S) {a : E → ℝ} (ha : ∀ e, 0 < a e) :
    ∃ ω : V → ℂ, (∀ i, ω i ^ G.rS S i = G.C0 S (fun e => (a e : ℂ)) i) ∧
      ∀ i, ∃ w : ℝ, 0 < w ∧ ω i = w := by
  have hq : ∀ α, ∃ q : ℝ, 0 < q ∧ G.q0 S (fun e => (a e : ℂ)) α = q := by
    intro α
    unfold q0
    split_ifs
    · exact ⟨a α.1, ha _, rfl⟩
    · exact ⟨(a α.1)⁻¹, inv_pos.2 (ha _), by simp⟩
  choose q hq0 hqe using hq
  set c : V → ℝ := fun i => (∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∈ S), q α) /
    ∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∉ S), q α
  have hc : ∀ i, 0 < c i := fun i =>
    div_pos (Finset.prod_pos fun α _ => hq0 α) (Finset.prod_pos fun α _ => hq0 α)
  have hC : ∀ i, G.C0 S (fun e => (a e : ℂ)) i = c i := by
    intro i
    simp only [C0, hqe, c]
    push_cast
    rfl
  refine ⟨fun i => ((c i ^ ((G.rS S i : ℝ)⁻¹) : ℝ) : ℂ), fun i => ?_,
    fun i => ⟨_, Real.rpow_pos_of_pos (hc i) _, rfl⟩⟩
  rw [hC, ← Complex.ofReal_pow, Real.rpow_inv_natCast_pow (hc i).le (G.rS_pos S hS i).ne']

/-- **Statewise real chart counts (`real:all-real-states`).** Fix real a_e>0, a_e≠1 on a loopless
graph. There are power-map charts, one for every state S and with positive real root tuple
ω_S (as in the proof of `real:strong-field-count`), such that for all sufficiently small real
p>0, at b=p⁻¹:
* (complex) the chart of S contributes exactly wt(S) solutions, the charts partition the Q(G)
  admissible complex solutions, and the charts of the states in a family T contain
  Σ_{states S∈T} wt(S) of them;
* (real) the chart of S contains exactly one real solution if every d_S(i) is even and none
  otherwise; all its wt(S) solutions are real iff every d_S(i)∈{0,2}; the admissible real
  solutions are exactly the real chart solutions of the Eulerian states; a real chart solution
  of S has negative messages exactly on the edges of S (negative-edge set S), so it is
  positive iff S=∅, and the chart of S is the sign sector S; the charts of the states in T
  contain #{Eulerian S∈T} real solutions, and there are #{Eulerian S} in total. -/
theorem exists_statewise_real_chart_counts (hG : G.Loopless) {a : E → ℝ} (ha : ∀ e, 0 < a e)
    (ha1 : ∀ e, a e ≠ 1) :
    ∃ (ω : Finset E → V → ℂ) (Q : Finset E → (V → ℂ) → Dart E → ℂ)
      (W : Finset E → (V → ℂ) → V → ℂ) (Φ : Finset E → OpenPartialHomeomorph (V → ℂ) (V → ℂ)),
      (∀ S, IsState G S → G.IsPowerMapChart S (fun e => (a e : ℂ)) (ω S) (Q S) (W S) (Φ S) ∧
        ∀ i, ∃ w : ℝ, 0 < w ∧ ω S i = w) ∧
      ∃ ε > 0, ∀ p : V → ℝ, (∀ i, 0 < p i) → (∀ i, p i < ε) →
        (∀ S, IsState G S →
          Nat.card (G.chartSols S (Q S) (W S) (fun i => (p i : ℂ))) = G.wt phi S) ∧
        (∀ y, G.IsAdmissibleSolution (fun e => (a e : ℂ)) (fun i => ((p i : ℂ))⁻¹) y ↔
          ∃ S, IsState G S ∧ y ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ))) ∧
        (∀ S S' y, IsState G S → IsState G S' →
          y ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ)) →
          y ∈ G.chartSols S' (Q S') (W S') (fun i => (p i : ℂ)) → S = S') ∧
        (∀ T : Finset (Finset E), Nat.card {y // ∃ S ∈ T.filter (IsState G),
            y ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ))} =
          ∑ S ∈ T.filter (IsState G), G.wt phi S) ∧
        Nat.card {y // G.IsAdmissibleSolution (fun e => (a e : ℂ)) (fun i => ((p i : ℂ))⁻¹) y} =
          G.Q ∧
        (∀ S, IsState G S → Nat.card {y : Dart E → ℝ //
            (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ))} =
          if G.IsEvenSet S then 1 else 0) ∧
        (∀ S, IsState G S → ((∀ y ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ)), ∀ α,
          (y α).im = 0) ↔ G.IsCycleUnion S)) ∧
        (∀ y : Dart E → ℝ, G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y ↔
          ∃ S, G.IsEvenSet S ∧
            (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ))) ∧
        (∀ S, IsState G S → ∀ y : Dart E → ℝ,
          (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ)) →
            negSupport y = S ∧ ((∀ α, 0 < y α) ↔ S = ∅)) ∧
        (∀ S, IsState G S → ∀ y : Dart E → ℝ, G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y →
          (negSupport y = S ↔
            (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ)))) ∧
        (∀ T : Finset (Finset E), Nat.card {y : Dart E → ℝ // ∃ S ∈ T.filter (IsState G),
            (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ))} =
          (T.filter G.IsEvenSet).card) ∧
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y} =
          (Finset.univ.filter G.IsEvenSet).card := by
  classical
  have haC : ∀ e, ((a e : ℂ)) ≠ 0 := fun e => by exact_mod_cast (ha e).ne'
  have haC1 : ∀ e, ((a e : ℂ)) ^ 2 ≠ 1 := by
    intro e h
    have h' : a e ^ 2 = 1 := by exact_mod_cast h
    have : (a e - 1) * (a e + 1) = 0 := by linear_combination h'
    rcases mul_eq_zero.1 this with h1 | h1
    · exact ha1 e (by linarith)
    · linarith [ha e]
  have hex : ∀ S : Finset E, ∃ (ω : V → ℂ) (Q : (V → ℂ) → Dart E → ℂ) (W : (V → ℂ) → V → ℂ)
      (Φ : OpenPartialHomeomorph (V → ℂ) (V → ℂ)), IsState G S →
        G.IsPowerMapChart S (fun e => (a e : ℂ)) ω Q W Φ ∧ ∀ i, ∃ w : ℝ, 0 < w ∧ ω i = w := by
    intro S
    by_cases hS : IsState G S
    · obtain ⟨ω, hω, hωpos⟩ := G.exists_pos_rootTuple hS ha
      have hω0 : ∀ i, ω i ≠ 0 := fun i => by
        obtain ⟨w, hw, hwe⟩ := hωpos i
        rw [hwe]
        exact_mod_cast hw.ne'
      obtain ⟨Q, W, Φ, hc⟩ := G.exists_isPowerMapChart hG hS haC haC1 hω hω0
      exact ⟨ω, Q, W, Φ, fun _ => ⟨hc, hωpos⟩⟩
    · exact ⟨0, 0, 0, OpenPartialHomeomorph.refl _, fun h => absurd h hS⟩
  choose ω Q W Φ hc using hex
  have hc' : ∀ S, IsState G S → G.IsPowerMapChart S (fun e => (a e : ℂ)) (ω S) (Q S) (W S) (Φ S) :=
    fun S hS => (hc S hS).1
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_statewise_partition hG haC haC1 hc'
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_statewise_real_partition hG ha ha1 hc' fun S hS => (hc S hS).2
  refine ⟨ω, Q, W, Φ, hc, min ε₁ ε₂, lt_min hε₁ hε₂, fun p hp hpε => ?_⟩
  obtain ⟨hcard, hpart, huniq, -⟩ := h₁ (fun i => (p i : ℂ)) (fun i => by simp [(hp i).ne'])
    (fun i => by
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hp i)]
      exact (hpε i).trans_le (min_le_left _ _))
  obtain ⟨hreal, hall, hrpart, hneg, hsector, hrT, hrtot⟩ :=
    h₂ p hp fun i => (hpε i).trans_le (min_le_right _ _)
  have hT := card_chartSols_union hcard huniq
  have htot : Nat.card {y // G.IsAdmissibleSolution (fun e => (a e : ℂ))
      (fun i => ((p i : ℂ))⁻¹) y} = G.Q := by
    rw [← G.sum_wt_states, ← hT Finset.univ]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by rw [hpart]; simp)
  exact ⟨hcard, hpart, huniq, hT, htot, hreal, hall, hrpart, hneg, hsector, hrT, hrtot⟩

/-- **The other real roots (`real:all-real-states`).** An Eulerian edge set that is not a union
of vertex-disjoint cycles has a vertex of degree at least four, and weight wt(S)≥3; by
`exists_statewise_real_chart_counts` exactly one of its wt(S) chart solutions is real. -/
theorem exists_four_le_deg_of_not_isCycleUnion {S : Finset E} (hE : G.IsEvenSet S)
    (hU : ¬ G.IsCycleUnion S) : (∃ v, 4 ≤ G.deg S v) ∧ 3 ≤ G.wt phi S := by
  simp only [IsCycleUnion, not_forall] at hU
  obtain ⟨v, hv⟩ := hU
  have h4 : 4 ≤ G.deg S v := by
    obtain ⟨m, hm⟩ := hE v
    omega
  exact ⟨⟨v, h4⟩, G.three_le_wt hE h4⟩

/-- **The generator states inject into the real roots (`real:all-real-states`).** The cycle-union
(generator) states are Eulerian, and they exhaust the Eulerian states, which index the real
roots at strong field, exactly when every Eulerian edge set is a cycle union. -/
theorem card_cycleUnions_eq_card_evenSets_iff :
    (Finset.univ.filter G.IsCycleUnion).card = (Finset.univ.filter G.IsEvenSet).card ↔
      ∀ S, G.IsEvenSet S → G.IsCycleUnion S := by
  have hsub : Finset.univ.filter G.IsCycleUnion ⊆ Finset.univ.filter G.IsEvenSet := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact hS.isEvenSet
  constructor
  · intro h S hS
    have heq := Finset.eq_of_subset_of_card_le hsub h.ge
    have : S ∈ Finset.univ.filter G.IsEvenSet := Finset.mem_filter.2 ⟨Finset.mem_univ _, hS⟩
    rw [← heq] at this
    exact (Finset.mem_filter.1 this).2
  · intro h
    congr 1
    exact Finset.filter_congr fun S _ => ⟨fun h' => h'.isEvenSet, h S⟩

end Assembly

end Multigraph

end BPFixedPoints
