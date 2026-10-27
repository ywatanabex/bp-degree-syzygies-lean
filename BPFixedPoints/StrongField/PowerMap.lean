import BPFixedPoints.StrongField.Simple

/-!
# Analytic power-map coordinates at strong fields (`sf:normal-form`, `sf:power-map`)

Fix a loopless graph, a state S, edge parameters a_e≠0 with a_e²≠1 and a root tuple ω with
ω_i^{r_i}=C_{S,i}(q⁰). The chart system of `StrongField/Chart.lean` is polynomial, hence
analytic (`analyticAt_chartMap`), so the analytic implicit function theorem of Mathlib
(`ContDiffAt.implicitFunction` with smoothness index ω) gives a branch ψ which is analytic near
(a,0) (`exists_chart_branch_analytic`). Restrict to the fixed a, write ψ(a,π)=(Q(π),W(π)) and
put Φ(π)=(π_i W(π)_i)_i. Since π=0 is a zero of every factor π_i, the derivative of Φ at 0 is
the diagonal matrix diag(ω), invertible because ω_i≠0 (`diagEquiv`); by the analytic inverse
function theorem Φ is an analytic chart with analytic inverse. In the paper's notation the Lean
π is the coordinate w of eq. `sf:power-map`, Φ(π)=f is the vertex coordinate, and
`IsPowerMapChart.unit_equations` shows W_i^{r_i}=C_{S,i}(Q) and f_i^{r_i}=(−1)^{k_i}p_iC_{S,i},
so π_i=f_iC_{S,i}^{−1/r_i} is the coordinate change `sf:coordinate-change`.

`exists_isPowerMapChart` bundles the result as `IsPowerMapChart`: on an open domain containing
0, Q and W are analytic, the chart equations hold, the BP messages y(π) are analytic across π=0,
and for π with all π_i≠0, y(π) is a simple admissible BP solution at b=p⁻¹ with p given exactly
by the power map p_i=(−1)^{k_i}π_i^{r_i} (`powerMap`). For all sufficiently small nonzero p, a
chart yields exactly wt(S)=∏ r_i distinct such solutions (`IsPowerMapChart.exists_card_solutions`,
assembled with the choice of ω in `exists_powerMap_normal_form`), and charts of different states
yield different solutions (`IsPowerMapChart.exists_chartY_ne`). The edge involution identity
`sf:edge-involution` is `edgeRes_involution`.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

open MvPolynomial Filter Topology

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section AnalyticBranch

variable (S : Finset E)

/-- The chart map is analytic at every point: each component is a polynomial in the chart
variables. -/
theorem analyticAt_chartMap (v : (E ⊕ V → ℂ) × (Dart E ⊕ V → ℂ)) :
    AnalyticAt ℂ (G.chartMap S) v := by
  have h : ∀ k, AnalyticAt ℂ
      (fun v : (E ⊕ V → ℂ) × (Dart E ⊕ V → ℂ) => eval (chartL v) (G.chartSys S k)) v := by
    intro k
    have h1 := AnalyticOnNhd.eval_continuousLinearMap (chartL (V := V) (E := E)) (G.chartSys S k)
    exact h1 v (Set.mem_univ _)
  have e : G.chartMap S = fun v k => eval (chartL v) (G.chartSys S k) := by
    funext v k; rw [chartL_apply]; rfl
  rw [e]
  exact AnalyticAt.pi h

variable {G S} {a : E → ℂ} {ω : V → ℂ}

/-- **Analytic statewise chart branches.** Same as `exists_chart_branch`, but the branch is
produced by the analytic implicit function theorem and is analytic at every parameter near
(a,0). -/
theorem exists_chart_branch_analytic (hS : IsState G S) (ha : ∀ e, a e ≠ 0)
    (hω : ∀ i, ω i ^ G.rS S i = G.C0 S a i) (hω0 : ∀ i, ω i ≠ 0) :
    ∃ ψ : (E ⊕ V → ℂ) → (Dart E ⊕ V → ℂ), ψ (Sum.elim a 0) = Sum.elim (G.q0 S a) ω ∧
      (∀ᶠ x in 𝓝 (Sum.elim a 0), AnalyticAt ℂ ψ x) ∧
      (∀ᶠ x in 𝓝 (Sum.elim a 0), G.chartMap S (x, ψ x) = 0) ∧
      (∀ᶠ v in 𝓝 (G.basePt S a ω), G.chartMap S v = 0 → ψ v.1 = v.2) := by
  have cdf : ContDiffAt ℂ (⊤ : WithTop ℕ∞) (G.chartMap S) (G.basePt S a ω) :=
    (G.analyticAt_chartMap S _).contDiffAt
  have pn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hfd : fderiv ℂ (G.chartMap S) (G.basePt S a ω) = G.chartDeriv S (G.basePt S a ω) :=
    (G.hasStrictFDerivAt_chartMap S _).hasFDerivAt.fderiv
  have if₂ : (fderiv ℂ (G.chartMap S) (G.basePt S a ω) ∘L
      ContinuousLinearMap.inr ℂ (E ⊕ V → ℂ) (Dart E ⊕ V → ℂ)).IsInvertible := by
    rw [hfd]; exact isInvertible_chartDeriv hS ha hω0
  refine ⟨cdf.implicitFunction pn if₂, cdf.implicitFunction_apply_self pn if₂,
    (cdf.contDiffAt_implicitFunction pn if₂).analyticAt.eventually_analyticAt, ?_, ?_⟩
  · have h := cdf.eventually_apply_implicitFunction pn if₂
    rw [chartMap_base ha hω] at h
    exact h
  · filter_upwards [cdf.eventually_apply_eq_iff_implicitFunction pn if₂] with v hv h
    rw [chartMap_base ha hω] at hv
    exact hv.1 h

end AnalyticBranch

section Diagonal

/-- Diagonal linear map δ ↦ (ω_i δ_i)_i on ℂ^V. -/
noncomputable def diagCLM (ω : V → ℂ) : (V → ℂ) →L[ℂ] (V → ℂ) :=
  ContinuousLinearMap.pi fun i => ω i • ContinuousLinearMap.proj i

/-- Coordinates of the diagonal map. -/
theorem diagCLM_apply (ω δ : V → ℂ) : diagCLM ω δ = fun i => ω i * δ i := by
  funext i; simp [diagCLM]

/-- The diagonal map with nonzero entries, as a linear automorphism of ℂ^V. -/
noncomputable def diagEquiv (ω : V → ℂ) (hω : ∀ i, ω i ≠ 0) : (V → ℂ) ≃L[ℂ] (V → ℂ) :=
  ContinuousLinearEquiv.equivOfInverse (diagCLM ω) (diagCLM fun i => (ω i)⁻¹)
    (fun δ => by funext i; simp [diagCLM_apply, hω i])
    (fun δ => by funext i; simp [diagCLM_apply, hω i])

/-- The underlying linear map of `diagEquiv` is `diagCLM`. -/
theorem coe_diagEquiv (ω : V → ℂ) (hω : ∀ i, ω i ≠ 0) :
    (diagEquiv ω hω : (V → ℂ) →L[ℂ] (V → ℂ)) = diagCLM ω := rfl

end Diagonal

section PowerMapChart

variable (S : Finset E)

/-- Power map p_i=(−1)^{k_i}π_i^{r_i} of eq. `sf:power-map`, with k_i=d_S(i). -/
noncomputable def powerMap (π : V → ℂ) (i : V) : ℂ := (-1) ^ G.deg S i * π i ^ G.rS S i

/-- **Statewise power-map chart (`sf:normal-form`).** For a state S, edge parameters a and a
root tuple ω, the data Q (dart messages), W (normalized vertex unknowns) and Φ form a power-map
chart if:
* Q, W are nonzero and analytic on the open set `Φ.source ∋ 0`, with Q(0)=q⁰ and W(0)=ω;
* `Φ π = (π_i W(π)_i)_i`, so Φ sends the power-map coordinate π (the paper's w) to the
  vertex coordinate f (inverse of eq. `sf:coordinate-change`); Φ is analytic with analytic
  inverse, Φ(0)=0, and its derivative at 0 is the invertible diagonal matrix diag(ω);
* (Q(π),W(π)) solves the chart system at (a,π), and is the only solution near (0,(q⁰,ω));
* the messages y(π)=`chartY S π (Q π, W π)` are analytic on `Φ.source`, including across π=0,
  where they equal `limY S a`;
* for π∈`Φ.source` with all π_i≠0, y(π) is a simple admissible BP solution at the edge
  parameters a and the external fields b_i=p_i⁻¹, where p=`powerMap S π` is exactly the power map
  p_i=(−1)^{k_i}π_i^{r_i} (eq. `sf:power-map`); its total fields are F_i=f_i or f_i⁻¹. -/
structure IsPowerMapChart (a : E → ℂ) (ω : V → ℂ)
    (Q : (V → ℂ) → Dart E → ℂ) (W : (V → ℂ) → V → ℂ)
    (Φ : OpenPartialHomeomorph (V → ℂ) (V → ℂ)) : Prop where
  /-- The base point π=0 lies in the chart domain. -/
  zero_mem : (0 : V → ℂ) ∈ Φ.source
  /-- Messages at π=0 are the positive-branch values q⁰. -/
  Q_zero : Q 0 = G.q0 S a
  /-- Normalized vertex unknowns at π=0 are the root tuple ω. -/
  W_zero : W 0 = ω
  /-- The messages are nonzero on the chart domain. -/
  Q_ne : ∀ π ∈ Φ.source, ∀ α, Q π α ≠ 0
  /-- The normalized vertex unknowns are nonzero on the chart domain. -/
  W_ne : ∀ π ∈ Φ.source, ∀ i, W π i ≠ 0
  /-- The messages are analytic on the chart domain. -/
  analyticOnNhd_Q : AnalyticOnNhd ℂ Q Φ.source
  /-- The normalized vertex unknowns are analytic on the chart domain. -/
  analyticOnNhd_W : AnalyticOnNhd ℂ W Φ.source
  /-- The coordinate change is f_i=π_i W(π)_i. -/
  coe_eq : ⇑Φ = fun π i => π i * W π i
  /-- The coordinate change fixes the origin. -/
  map_zero : Φ 0 = 0
  /-- The coordinate change is analytic. -/
  analyticOnNhd : AnalyticOnNhd ℂ Φ Φ.source
  /-- Its inverse is analytic. -/
  analyticOnNhd_symm : AnalyticOnNhd ℂ Φ.symm Φ.target
  /-- Its derivative at the origin is diag(ω). -/
  hasFDerivAt : HasFDerivAt Φ (diagCLM ω) 0
  /-- The chart equations hold on the chart domain. -/
  sol : ∀ π ∈ Φ.source, G.chartMap S (Sum.elim a π, Sum.elim (Q π) (W π)) = 0
  /-- Near the base point, every chart solution is the chart point. -/
  unique : ∀ᶠ v in 𝓝 ((0 : V → ℂ), Sum.elim (G.q0 S a) ω),
    G.chartMap S (Sum.elim a v.1, v.2) = 0 → v.2 = Sum.elim (Q v.1) (W v.1)
  /-- The BP messages are analytic on the chart domain, across π=0. -/
  analyticOnNhd_Y : AnalyticOnNhd ℂ (fun π => G.chartY S π (Sum.elim (Q π) (W π))) Φ.source
  /-- At π=0 the BP messages are the boundary limit: zero on S and q⁰ off S. -/
  Y_zero : G.chartY S 0 (Sum.elim (Q 0) (W 0)) = G.limY S a
  /-- Admissible BP solutions at the power-map parameter. -/
  admissible : ∀ π ∈ Φ.source, (∀ i, π i ≠ 0) →
    G.IsAdmissibleSolution a (fun i => (G.powerMap S π i)⁻¹)
      (G.chartY S π (Sum.elim (Q π) (W π)))
  /-- These solutions are simple. -/
  simple : ∀ π ∈ Φ.source, (∀ i, π i ≠ 0) →
    G.IsSimpleSolution a (fun i => (G.powerMap S π i)⁻¹) (G.chartY S π (Sum.elim (Q π) (W π)))
  /-- Their total fields are the chart fields F_i. -/
  totalField_eq : ∀ π ∈ Φ.source, (∀ i, π i ≠ 0) → ∀ i,
    G.totalField (fun i => (G.powerMap S π i)⁻¹) (G.chartY S π (Sum.elim (Q π) (W π))) i =
      G.chartF S π (Sum.elim (Q π) (W π)) i

variable {G S}

/-- The chart field b=(−1)^k/π^r is the reciprocal of the power map. -/
theorem chartB_eq_inv_powerMap (π : V → ℂ) :
    G.chartB S π = fun i => (G.powerMap S π i)⁻¹ := by
  funext i
  unfold chartB powerMap
  rw [mul_inv, ← inv_pow, inv_neg, inv_one, div_eq_mul_inv]

/-- The parameter embedding π ↦ (a,π) is analytic. -/
theorem analyticAt_sumElim (a : E → ℂ) (π : V → ℂ) :
    AnalyticAt ℂ (fun π : V → ℂ => (Sum.elim a π : E ⊕ V → ℂ)) π := by
  refine AnalyticAt.pi (f := fun j (π : V → ℂ) => Sum.elim a π j) fun j => ?_
  rcases j with e | i
  · exact analyticAt_const
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : V => ℂ) i).analyticAt π

/-- The parameter embedding π ↦ (a,π) is continuous. -/
theorem continuous_sumElim (a : E → ℂ) :
    Continuous fun π : V → ℂ => (Sum.elim a π : E ⊕ V → ℂ) :=
  continuous_pi fun j => by
    rcases j with e | i
    · exact continuous_const
    · exact continuous_apply i

variable {a : E → ℂ} {ω : V → ℂ}

/-- **Analytic power-map coordinates (`sf:normal-form`, eqs. `sf:coordinate-change`,
`sf:power-map`).** For a loopless graph, a state S, edge parameters a_e≠0 with a_e²≠1 and a root
tuple ω_i^{r_i}=C_{S,i}(q⁰), ω_i≠0, a statewise power-map chart exists. -/
theorem exists_isPowerMapChart (hG : G.Loopless) (hS : IsState G S) (ha : ∀ e, a e ≠ 0)
    (ha1 : ∀ e, a e ^ 2 ≠ 1) (hω : ∀ i, ω i ^ G.rS S i = G.C0 S a i) (hω0 : ∀ i, ω i ≠ 0) :
    ∃ (Q : (V → ℂ) → Dart E → ℂ) (W : (V → ℂ) → V → ℂ)
      (Φ : OpenPartialHomeomorph (V → ℂ) (V → ℂ)), G.IsPowerMapChart S a ω Q W Φ := by
  obtain ⟨ψ, hψ0, hψa, hψs, hψu⟩ := exists_chart_branch_analytic hS ha hω hω0
  have hψc : ∀ᶠ x in 𝓝 (Sum.elim a 0), ContinuousAt ψ x := hψa.mono fun x hx => hx.continuousAt
  have hgood := eventually_goodAt ha ha1 hψ0 hω0 hψc hψs hS
  have hc0 : ContinuousAt ψ (Sum.elim a 0) := hψc.self_of_nhds
  -- Nonsingularity of the normalized Jacobian near the base point.
  have hdet : ∀ᶠ x in 𝓝 (Sum.elim a 0), (G.normC S x (ψ x)).det ≠ 0 := by
    have hcN := continuousAt_normC (S := S) ha hψ0 hc0
    have hc := ((continuous_id.matrix_det).continuousAt).comp hcN
    have h0 : (G.normC S (Sum.elim a 0) (ψ (Sum.elim a 0))).det ≠ 0 := by
      rw [hψ0, normC_base]; exact G.det_normLim_ne_zero S hS
    exact hc.eventually_ne h0
  have hden : ∀ᶠ x in 𝓝 (Sum.elim a 0), ∀ α, α.1 ∈ S → G.denS S x (ψ x) α ≠ 0 := by
    refine Filter.eventually_all.2 fun α => ?_
    by_cases hα : α.1 ∈ S
    · have hcq : ∀ v, ContinuousAt (fun x => ψ x v) (Sum.elim a 0) := fun v =>
        (continuous_apply v).continuousAt.comp hc0
      have hcx : ∀ j, ContinuousAt (fun x : E ⊕ V → ℂ => x j) (Sum.elim a 0) := fun j =>
        (continuous_apply j).continuousAt
      have hq : ψ (Sum.elim a 0) (Sum.inl α) ≠ 0 := by rw [hψ0]; exact q0_ne_zero ha α
      have hc : ContinuousAt (fun x => G.denS S x (ψ x) α) (Sum.elim a 0) := by
        unfold denS
        exact ((((hcx _).mul (hcq _)).neg.div (hcq _) hq).sub (hcx _)).mul (hcq _).neg
      have h0 : G.denS S (Sum.elim a 0) (ψ (Sum.elim a 0)) α ≠ 0 := by
        rw [hψ0]; exact denS_base ha hα
      exact (hc.eventually_ne h0).mono fun x hx _ => hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hα
  -- Pull back along π ↦ (a,π).
  have hι : Tendsto (fun π : V → ℂ => (Sum.elim a π : E ⊕ V → ℂ)) (𝓝 0) (𝓝 (Sum.elim a 0)) :=
    (continuous_sumElim a).tendsto 0
  have hall : ∀ᶠ π in 𝓝 (0 : V → ℂ), AnalyticAt ℂ ψ (Sum.elim a π) ∧
      GoodAt G S ψ (Sum.elim a π) ∧ (G.normC S (Sum.elim a π) (ψ (Sum.elim a π))).det ≠ 0 ∧
      ∀ α, α.1 ∈ S → G.denS S (Sum.elim a π) (ψ (Sum.elim a π)) α ≠ 0 :=
    hι.eventually (hψa.and (hgood.and (hdet.and hden)))
  set Q : (V → ℂ) → Dart E → ℂ := fun π α => ψ (Sum.elim a π) (Sum.inl α) with hQdef
  set W : (V → ℂ) → V → ℂ := fun π i => ψ (Sum.elim a π) (Sum.inr i) with hWdef
  have hZ : ∀ π, Sum.elim (Q π) (W π) = ψ (Sum.elim a π) := fun π => by
    funext k; rcases k with α | i <;> rfl
  have hZa : ∀ π, AnalyticAt ℂ ψ (Sum.elim a π) →
      AnalyticAt ℂ (fun π : V → ℂ => ψ (Sum.elim a π)) π := fun π h =>
    h.comp (analyticAt_sumElim a π)
  have hcomp : ∀ π, AnalyticAt ℂ ψ (Sum.elim a π) → ∀ k,
      AnalyticAt ℂ (fun π : V → ℂ => ψ (Sum.elim a π) k) π := fun π h k =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Dart E ⊕ V => ℂ) k).analyticAt _ |>.comp
      (hZa π h)
  have hQa : ∀ π, AnalyticAt ℂ ψ (Sum.elim a π) → AnalyticAt ℂ Q π := fun π h =>
    AnalyticAt.pi (f := fun α π => Q π α) fun α => hcomp π h (Sum.inl α)
  have hWa : ∀ π, AnalyticAt ℂ ψ (Sum.elim a π) → AnalyticAt ℂ W π := fun π h =>
    AnalyticAt.pi (f := fun i π => W π i) fun i => hcomp π h (Sum.inr i)
  have hπa : ∀ (i : V) (π : V → ℂ), AnalyticAt ℂ (fun π : V → ℂ => π i) π := fun i π =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : V => ℂ) i).analyticAt π
  -- The coordinate change φ(π)=(π_i W(π)_i)_i.
  set φ : (V → ℂ) → V → ℂ := fun π i => π i * W π i with hφdef
  have hφa : ∀ π, AnalyticAt ℂ ψ (Sum.elim a π) → AnalyticAt ℂ φ π := fun π h =>
    AnalyticAt.pi (f := fun i π => φ π i) fun i => (hπa i π).mul (hcomp π h (Sum.inr i))
  have hW0 : W 0 = ω := by
    funext i; simp only [hWdef]; rw [hψ0]; rfl
  have hQ0 : Q 0 = G.q0 S a := by
    funext α; simp only [hQdef]; rw [hψ0]; rfl
  have hφ0 : φ 0 = 0 := by funext i; simp [hφdef]
  have ha0 : AnalyticAt ℂ ψ (Sum.elim a 0) := hall.self_of_nhds.1
  have hφd : HasFDerivAt φ ((diagEquiv ω hω0 : (V → ℂ) →L[ℂ] (V → ℂ))) 0 := by
    rw [coe_diagEquiv, diagCLM]
    refine hasFDerivAt_pi.2 fun i => ?_
    have hWi : HasFDerivAt (fun π : V → ℂ => W π i)
        (fderiv ℂ (fun π : V → ℂ => W π i) 0) 0 :=
      (hcomp 0 ha0 (Sum.inr i)).differentiableAt.hasFDerivAt
    have h := (hasFDerivAt_apply (𝕜 := ℂ) i (0 : V → ℂ)).fun_mul hWi
    convert h using 1
    rw [hW0]
    simp
  have pn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have cdφ : ContDiffAt ℂ (⊤ : WithTop ℕ∞) φ 0 := (hφa 0 ha0).contDiffAt
  set Φ₀ := cdφ.toOpenPartialHomeomorph φ hφd pn
  have hsymm0 : AnalyticAt ℂ Φ₀.symm 0 := by
    have h := (cdφ.to_localInverse hφd pn).analyticAt
    rw [hφ0] at h
    exact h
  -- Open sets.
  obtain ⟨U, hUsub, hUo, hU0⟩ := mem_nhds_iff.1 hall
  obtain ⟨T, hTsub, hTo, hT0⟩ := mem_nhds_iff.1 hsymm0.eventually_analyticAt
  have hso : IsOpen (U ∩ (Φ₀.source ∩ Φ₀ ⁻¹' T)) := hUo.inter (Φ₀.isOpen_inter_preimage hTo)
  set Φ := Φ₀.restrOpen _ hso
  have hΦcoe : ⇑Φ = φ := rfl
  have hΦsymm : ⇑Φ.symm = ⇑Φ₀.symm := rfl
  have hsrc : ∀ π ∈ Φ.source, AnalyticAt ℂ ψ (Sum.elim a π) ∧
      GoodAt G S ψ (Sum.elim a π) ∧ (G.normC S (Sum.elim a π) (ψ (Sum.elim a π))).det ≠ 0 ∧
      ∀ α, α.1 ∈ S → G.denS S (Sum.elim a π) (ψ (Sum.elim a π)) α ≠ 0 := by
    intro π hπ
    rw [OpenPartialHomeomorph.restrOpen_source] at hπ
    exact hUsub hπ.2.1
  have hY : ∀ π, AnalyticAt ℂ ψ (Sum.elim a π) → (∀ α, ψ (Sum.elim a π) (Sum.inl α) ≠ 0) →
      AnalyticAt ℂ (fun π => G.chartY S π (Sum.elim (Q π) (W π))) π := by
    intro π h hq
    refine AnalyticAt.pi (f := fun α π => G.chartY S π (Sum.elim (Q π) (W π)) α) fun α => ?_
    by_cases hα : α.1 ∈ S
    · have hh : G.deg S (G.head α) ≠ 0 := deg_ne_zero_of_mem hα (head_incident α)
      have e : (fun π => G.chartY S π (Sum.elim (Q π) (W π)) α) =
          fun π => -(π (G.head α) * W π (G.head α)) / Q π α := by
        funext π; simp [chartY, chartF, hα, hh]
      rw [e]
      exact (((hπa _ π).mul (hcomp π h (Sum.inr _))).neg).div (hcomp π h (Sum.inl α)) (hq α)
    · have e : (fun π => G.chartY S π (Sum.elim (Q π) (W π)) α) = fun π => Q π α := by
        funext π; simp [chartY, hα]
      rw [e]
      exact hcomp π h (Sum.inl α)
  refine ⟨Q, W, Φ, ?_⟩
  exact
    { zero_mem := by
        rw [OpenPartialHomeomorph.restrOpen_source]
        refine ⟨cdφ.mem_toOpenPartialHomeomorph_source hφd pn, hU0,
          cdφ.mem_toOpenPartialHomeomorph_source hφd pn, ?_⟩
        show φ 0 ∈ T
        rw [hφ0]; exact hT0
      Q_zero := hQ0
      W_zero := hW0
      Q_ne := fun π hπ α => (hsrc π hπ).2.1.q_ne α
      W_ne := fun π hπ i => (hsrc π hπ).2.1.w_ne i
      analyticOnNhd_Q := fun π hπ => hQa π (hsrc π hπ).1
      analyticOnNhd_W := fun π hπ => hWa π (hsrc π hπ).1
      coe_eq := hΦcoe
      map_zero := hφ0
      analyticOnNhd := fun π hπ => by rw [hΦcoe]; exact hφa π (hsrc π hπ).1
      analyticOnNhd_symm := fun y hy => by
        have h1 := Φ.map_target hy
        have h2 := Φ.right_inv hy
        rw [OpenPartialHomeomorph.restrOpen_source] at h1
        have h3 : Φ (Φ.symm y) ∈ T := h1.2.2.2
        rw [h2] at h3
        rw [hΦsymm]
        exact hTsub h3
      hasFDerivAt := by rw [hΦcoe, ← coe_diagEquiv ω hω0]; exact hφd
      sol := fun π hπ => by rw [hZ]; exact (hsrc π hπ).2.1.sol
      unique := by
        have hg : Tendsto (fun v : (V → ℂ) × (Dart E ⊕ V → ℂ) => (Sum.elim a v.1, v.2))
            (𝓝 ((0 : V → ℂ), Sum.elim (G.q0 S a) ω)) (𝓝 (G.basePt S a ω)) :=
          (((continuous_sumElim a).comp continuous_fst).prodMk continuous_snd).tendsto _
        filter_upwards [hg.eventually hψu] with v hv h
        rw [hZ]
        exact (hv h).symm
      analyticOnNhd_Y := fun π hπ => hY π (hsrc π hπ).1 (hsrc π hπ).2.1.q_ne
      Y_zero := by
        funext α
        rw [hQ0, hW0]
        unfold chartY limY chartF
        by_cases hα : α.1 ∈ S
        · have hh : G.deg S (G.head α) ≠ 0 := deg_ne_zero_of_mem hα (head_incident α)
          simp [hα, hh]
        · simp [hα]
      admissible := fun π hπ hπ0 => by
        have h := ((hsrc π hπ).2.1.admissible hG hS hπ0).1
        rw [← hZ, chartB_eq_inv_powerMap] at h
        exact h
      simple := fun π hπ hπ0 => by
        have h := G.isSimple_of_det_normC hG hS (hsrc π hπ).2.1 hπ0 (hsrc π hπ).2.2.2
          (hsrc π hπ).2.2.1
        rw [← hZ, chartB_eq_inv_powerMap] at h
        exact h
      totalField_eq := fun π hπ hπ0 => by
        have h := ((hsrc π hπ).2.1.admissible hG hS hπ0).2
        rw [← hZ, chartB_eq_inv_powerMap] at h
        exact h }

end PowerMapChart

section Counting

variable {S S' : Finset E} {a : E → ℂ} {ω ω' : V → ℂ} {Q Q' : (V → ℂ) → Dart E → ℂ}
  {W W' : (V → ℂ) → V → ℂ} {Φ Φ' : OpenPartialHomeomorph (V → ℂ) (V → ℂ)}

/-- ‖p_i‖=‖π_i‖^{r_i} for the power map. -/
theorem norm_powerMap (π : V → ℂ) (i : V) : ‖G.powerMap S π i‖ = ‖π i‖ ^ G.rS S i := by
  simp [powerMap, norm_pow]

/-- Small power-map values force small roots: for every δ>0 there is ε>0 such that
‖p_i‖<ε for all i implies ‖π‖<δ. -/
theorem exists_norm_lt_of_powerMap (hS : IsState G S) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ π : V → ℂ, (∀ i, ‖G.powerMap S π i‖ < ε) → ‖π‖ < δ := by
  set d := min δ 1
  have hd0 : 0 < d := lt_min hδ one_pos
  have hd1 : d ≤ 1 := min_le_right _ _
  set N := ∑ i, G.rS S i
  refine ⟨d ^ N, pow_pos hd0 N, fun π hπ => (pi_norm_lt_iff hδ).2 fun i => ?_⟩
  have hN : G.rS S i ≤ N := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have h1 : ‖π i‖ ^ G.rS S i < d ^ G.rS S i := by
    rw [← norm_powerMap]
    exact (hπ i).trans_le (pow_le_pow_of_le_one hd0.le hd1 hN)
  have h2 := (pow_lt_pow_iff_left₀ (norm_nonneg _) hd0.le (G.rS_pos S hS i).ne').1 h1
  exact h2.trans_le (min_le_left _ _)

/-- The power-map equation p=(−1)^kπ^r is the root equation π^r=(−1)^k p. -/
theorem powerMap_eq_iff (π p : V → ℂ) :
    G.powerMap S π = p ↔ ∀ i, π i ^ G.rS S i = (-1) ^ G.deg S i * p i := by
  have hsq : ∀ k : ℕ, ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := fun k => by
    rw [← mul_pow]; norm_num
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  unfold powerMap
  constructor
  · intro h; rw [← h, ← mul_assoc, hsq, one_mul]
  · intro h; rw [h, ← mul_assoc, hsq, one_mul]

/-- Points of a fiber over p with all p_i≠0 have all π_i≠0. -/
theorem ne_zero_of_powerMap_eq (hS : IsState G S) {π p : V → ℂ} (h : G.powerMap S π = p)
    (hp : ∀ i, p i ≠ 0) (i : V) : π i ≠ 0 := by
  intro h0
  apply hp i
  rw [← h]
  simp [powerMap, h0, zero_pow (G.rS_pos S hS i).ne']

/-- For p with all p_i≠0, the power map has exactly wt(S)=∏ r_i points in its fiber. -/
theorem card_powerMap_fiber (hS : IsState G S) {p : V → ℂ} (hp : ∀ i, p i ≠ 0) :
    Nat.card {π : V → ℂ // G.powerMap S π = p} = ∏ i, G.rS S i := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun π => G.powerMap_eq_iff π p),
    Nat.card_congr (Equiv.subtypePiEquivPi
      (p := fun i (x : ℂ) => x ^ G.rS S i = (-1) ^ G.deg S i * p i)), Nat.card_pi]
  exact Finset.prod_congr rfl fun i _ => card_pow_eq _ (G.rS_pos S hS i) _
    (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (hp i))

/-- The analytic unit C_{S,i}(q)=∏_{α→i,α∈S}q_α/∏_{α→i,α∉S}q_α of eq. `sf:units`, evaluated
at positive-branch messages q; at q=q⁰ it is `C0`. -/
noncomputable def unitC (S : Finset E) (q : Dart E → ℂ) (i : V) : ℂ :=
  (∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∈ S), q α) /
    ∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∉ S), q α

/-- The unit at the base messages is `C0`. -/
theorem unitC_q0 (S : Finset E) (a : E → ℂ) : G.unitC S (G.q0 S a) = G.C0 S a := rfl

variable {G}

/-- Two chart points over the same parameter with the same BP messages coincide. -/
theorem IsPowerMapChart.eq_of_chartY_eq (hc : G.IsPowerMapChart S a ω Q W Φ) {π π' : V → ℂ}
    (hπ : π ∈ Φ.source) (hπ' : π' ∈ Φ.source) (h0 : ∀ i, π i ≠ 0) (h0' : ∀ i, π' i ≠ 0)
    (hp : G.powerMap S π = G.powerMap S π')
    (hy : G.chartY S π (Sum.elim (Q π) (W π)) = G.chartY S π' (Sum.elim (Q π') (W π'))) :
    π = π' := by
  have hf : ∀ i, π i * W π i = π' i * W π' i := by
    intro i
    have e1 := hc.totalField_eq π hπ h0 i
    have e2 := hc.totalField_eq π' hπ' h0' i
    rw [hp, hy, e2] at e1
    unfold chartF at e1
    simp only [Sum.elim_inr] at e1
    split_ifs at e1
    · exact (inv_injective e1).symm
    · exact e1.symm
  apply Φ.injOn hπ hπ'
  rw [hc.coe_eq]
  funext i
  exact hf i

/-- **wt(S) points in each chart fiber.** For all sufficiently small nonzero p, every root π of
the power map p=(−1)^kπ^r lies in the chart domain, and there are exactly wt(S)=∏ r_i of
them. -/
theorem IsPowerMapChart.exists_card_fiber (hS : IsState G S)
    (hc : G.IsPowerMapChart S a ω Q W Φ) :
    ∃ ε > 0, ∀ p : V → ℂ, (∀ i, p i ≠ 0) → (∀ i, ‖p i‖ < ε) →
      (∀ π, G.powerMap S π = p → π ∈ Φ.source) ∧
      Nat.card {π : V → ℂ // π ∈ Φ.source ∧ G.powerMap S π = p} = ∏ i, G.rS S i := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 Φ.open_source 0 hc.zero_mem
  obtain ⟨ε, hε, hsmall⟩ := G.exists_norm_lt_of_powerMap hS hδ
  refine ⟨ε, hε, fun p hp hpε => ?_⟩
  have hin : ∀ π, G.powerMap S π = p → π ∈ Φ.source := fun π h => hball (by
    rw [Metric.mem_ball, dist_zero_right]
    exact hsmall π fun i => by rw [h]; exact hpε i)
  refine ⟨hin, ?_⟩
  rw [← G.card_powerMap_fiber hS hp]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun π => ⟨fun h => h.2, fun h => ⟨hin π h, h⟩⟩)

/-- **wt(S) distinct simple admissible BP solutions from each chart (`sf:normal-form`).** For
all sufficiently small nonzero p, the chart points over p give exactly wt(S)=∏ r_i distinct BP
message vectors, and each is a simple admissible BP solution at (a,b) with b_i=p_i⁻¹. -/
theorem IsPowerMapChart.exists_card_solutions (hS : IsState G S)
    (hc : G.IsPowerMapChart S a ω Q W Φ) :
    ∃ ε > 0, ∀ p : V → ℂ, (∀ i, p i ≠ 0) → (∀ i, ‖p i‖ < ε) →
      Nat.card {y : Dart E → ℂ //
        ∃ π, G.powerMap S π = p ∧ G.chartY S π (Sum.elim (Q π) (W π)) = y} = ∏ i, G.rS S i ∧
      ∀ π, G.powerMap S π = p →
        G.IsAdmissibleSolution a (fun i => (p i)⁻¹) (G.chartY S π (Sum.elim (Q π) (W π))) ∧
        G.IsSimpleSolution a (fun i => (p i)⁻¹) (G.chartY S π (Sum.elim (Q π) (W π))) := by
  obtain ⟨ε, hε, h⟩ := hc.exists_card_fiber hS
  refine ⟨ε, hε, fun p hp hpε => ?_⟩
  obtain ⟨hin, -⟩ := h p hp hpε
  have hnz := fun π (hπ : G.powerMap S π = p) => G.ne_zero_of_powerMap_eq hS hπ hp
  let f : {π : V → ℂ // G.powerMap S π = p} → {y : Dart E → ℂ //
      ∃ π, G.powerMap S π = p ∧ G.chartY S π (Sum.elim (Q π) (W π)) = y} :=
    fun π => ⟨G.chartY S π.1 (Sum.elim (Q π.1) (W π.1)), π.1, π.2, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun π π' hππ' => Subtype.ext ?_, fun y => ?_⟩
    · exact hc.eq_of_chartY_eq (hin _ π.2) (hin _ π'.2) (hnz _ π.2) (hnz _ π'.2)
        (π.2.trans π'.2.symm) (congrArg Subtype.val hππ')
    · obtain ⟨π, hπ, hy⟩ := y.2
      exact ⟨⟨π, hπ⟩, Subtype.ext hy⟩
  refine ⟨?_, fun π hπ => ?_⟩
  · rw [← Nat.card_congr (Equiv.ofBijective f hf), G.card_powerMap_fiber hS hp]
  · have e : (fun i => (G.powerMap S π i)⁻¹) = fun i => (p i)⁻¹ := by rw [hπ]
    have h1 := hc.admissible π (hin π hπ) (hnz π hπ)
    have h2 := hc.simple π (hin π hπ) (hnz π hπ)
    rw [e] at h1 h2
    exact ⟨h1, h2⟩

/-- **Unit equations (`sf:unit-equations`, `sf:coordinate-change`).** On the chart domain,
W(π)_i is an r_i-th root of the unit C_{S,i}(Q(π)), so π_i=f_i/W(π)_i with f=Φ(π) is the
coordinate change f_i C_{S,i}^{−1/r_i}, and f_i^{r_i}=(−1)^{k_i}p_i C_{S,i} with
p=`powerMap S π`. -/
theorem IsPowerMapChart.unit_equations (hc : G.IsPowerMapChart S a ω Q W Φ) {π : V → ℂ}
    (hπ : π ∈ Φ.source) (i : V) :
    W π i ^ G.rS S i = G.unitC S (Q π) i ∧
      Φ π i ^ G.rS S i = (-1) ^ G.deg S i * G.powerMap S π i * G.unitC S (Q π) i := by
  have h := congrFun (hc.sol π hπ) (Sum.inr i)
  simp only [chartMap, chartSys, chartVertex, vQ, vW, map_sub, map_mul, map_pow, map_prod,
    eval_X, Sum.elim_inr, Sum.elim_inl, Pi.zero_apply] at h
  have hP : ∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∉ S), Q π α ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun α _ => hc.Q_ne π hπ α
  have h1 : W π i ^ G.rS S i = G.unitC S (Q π) i := by
    rw [unitC, eq_div_iff hP]
    linear_combination h
  refine ⟨h1, ?_⟩
  have hsq : ((-1 : ℂ) ^ G.deg S i) * (-1) ^ G.deg S i = 1 := by rw [← mul_pow]; norm_num
  rw [hc.coe_eq, mul_pow, h1, powerMap, ← mul_assoc, hsq, one_mul]

/-- The BP messages of a chart are continuous at π=0, with value the boundary limit. -/
theorem IsPowerMapChart.continuousAt_chartY (hc : G.IsPowerMapChart S a ω Q W Φ) (α : Dart E) :
    ContinuousAt (fun π => G.chartY S π (Sum.elim (Q π) (W π)) α) 0 ∧
      G.chartY S 0 (Sum.elim (Q 0) (W 0)) α = G.limY S a α :=
  ⟨(continuous_apply α).continuousAt.comp (hc.analyticOnNhd_Y 0 hc.zero_mem).continuousAt,
    by rw [hc.Y_zero]⟩

/-- **Different states give different solutions (`sf:normal-form`).** For charts of two states
S≠S', for all sufficiently small nonzero p the BP messages of the two charts over p differ. -/
theorem IsPowerMapChart.exists_chartY_ne (hS : IsState G S) (hS' : IsState G S')
    (ha : ∀ e, a e ≠ 0) (hc : G.IsPowerMapChart S a ω Q W Φ)
    (hc' : G.IsPowerMapChart S' a ω' Q' W' Φ') (hSS : S ≠ S') :
    ∃ ε > 0, ∀ p : V → ℂ, (∀ i, ‖p i‖ < ε) → ∀ π π', G.powerMap S π = p →
      G.powerMap S' π' = p →
      G.chartY S π (Sum.elim (Q π) (W π)) ≠ G.chartY S' π' (Sum.elim (Q' π') (W' π')) := by
  obtain ⟨e, he⟩ : ∃ e, ¬ (e ∈ S ↔ e ∈ S') := by
    by_contra h
    push Not at h
    exact hSS (Finset.ext h)
  set α : Dart E := (e, true)
  have hlim : G.limY S a α ≠ G.limY S' a α := by
    by_cases h1 : e ∈ S
    · have h2 : e ∉ S' := fun h2 => he ⟨fun _ => h2, fun _ => h1⟩
      rw [limY_eq_zero G (S := S) (a := a) (α := α) h1]
      exact (limY_ne_zero G ha (S := S') (α := α) h2).symm
    · have h2 : e ∈ S' := by
        by_contra h2
        exact he ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      rw [limY_eq_zero G (S := S') (a := a) (α := α) h2]
      exact limY_ne_zero G ha (S := S) (α := α) h1
  set η := dist (G.limY S a α) (G.limY S' a α) / 2
  have hη : 0 < η := half_pos (dist_pos.2 hlim)
  obtain ⟨hc1, hv1⟩ := hc.continuousAt_chartY α
  obtain ⟨hc2, hv2⟩ := hc'.continuousAt_chartY α
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousAt_iff.1 hc1 η hη
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousAt_iff.1 hc2 η hη
  obtain ⟨ε₁, hε₁, hs₁⟩ := G.exists_norm_lt_of_powerMap hS hδ₁
  obtain ⟨ε₂, hε₂, hs₂⟩ := G.exists_norm_lt_of_powerMap hS' hδ₂
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun p hpε π π' hπ hπ' hy => ?_⟩
  have d₁ := h₁ (x := π) (by
    rw [dist_zero_right]
    exact hs₁ π fun i => by rw [hπ]; exact (hpε i).trans_le (min_le_left _ _))
  have d₂ := h₂ (x := π') (by
    rw [dist_zero_right]
    exact hs₂ π' fun i => by rw [hπ']; exact (hpε i).trans_le (min_le_right _ _))
  rw [hv1] at d₁
  rw [hv2, ← hy] at d₂
  have := dist_triangle_left (G.limY S a α) (G.limY S' a α)
    (G.chartY S π (Sum.elim (Q π) (W π)) α)
  have hηdef : η = dist (G.limY S a α) (G.limY S' a α) / 2 := rfl
  linarith

end Counting

section NormalForm

variable {S : Finset E} {a : E → ℂ}

/-- **Statewise power-map model (`sf:normal-form`).** For a loopless graph, a state S and edge
parameters a_e≠0 with a_e²≠1, there is a power-map chart (analytic BP messages across p=0 in
coordinates π in which the parameter map is exactly p_i=(−1)^{k_i}π_i^{r_i}), and for all
sufficiently small nonzero p this chart gives exactly wt(S)=∏ r_i distinct simple admissible BP
solutions at (a,b=p⁻¹). Distinctness across states is `IsPowerMapChart.exists_chartY_ne`. -/
theorem exists_powerMap_normal_form (hG : G.Loopless) (hS : IsState G S) (ha : ∀ e, a e ≠ 0)
    (ha1 : ∀ e, a e ^ 2 ≠ 1) :
    ∃ (ω : V → ℂ) (Q : (V → ℂ) → Dart E → ℂ) (W : (V → ℂ) → V → ℂ)
      (Φ : OpenPartialHomeomorph (V → ℂ) (V → ℂ)), G.IsPowerMapChart S a ω Q W Φ ∧
      ∃ ε > 0, ∀ p : V → ℂ, (∀ i, p i ≠ 0) → (∀ i, ‖p i‖ < ε) →
        Nat.card {y : Dart E → ℂ //
          ∃ π, G.powerMap S π = p ∧ G.chartY S π (Sum.elim (Q π) (W π)) = y} = ∏ i, G.rS S i ∧
        ∀ π, G.powerMap S π = p →
          G.IsAdmissibleSolution a (fun i => (p i)⁻¹) (G.chartY S π (Sum.elim (Q π) (W π))) ∧
          G.IsSimpleSolution a (fun i => (p i)⁻¹) (G.chartY S π (Sum.elim (Q π) (W π))) := by
  choose ω hω using fun i => IsAlgClosed.exists_pow_nat_eq (G.C0 S a i) (G.rS_pos S hS i)
  have hω0 : ∀ i, ω i ≠ 0 := fun i h => by
    have := hω i
    rw [h, zero_pow (G.rS_pos S hS i).ne'] at this
    exact C0_ne_zero ha i this.symm
  obtain ⟨Q, W, Φ, hc⟩ := G.exists_isPowerMapChart hG hS ha ha1 hω hω0
  exact ⟨ω, Q, W, Φ, hc, hc.exists_card_solutions hS⟩

end NormalForm

section EdgeInvolution

variable {K : Type*} [Field K]

/-- Edge residual R_i(y)=y_i(F_i+a y_j)−aF_i−y_j of an edge e={i,j} with parameter a, for the
message y_i=y_{i→j} and the opposite message y_j=y_{j→i}. -/
def edgeRes (A Fi yi yj : K) : K := yi * (Fi + A * yj) - A * Fi - yj

/-- **Edge involution (`sf:edge-involution`).** With ι(y_i,y_j)=(−F_j/y_i,−F_i/y_j),
R_i(ιy)=−F_i/(y_i y_j)·R_j(y) and R_j(ιy)=−F_j/(y_i y_j)·R_i(y). -/
theorem edgeRes_involution {A Fi Fj yi yj : K} (hi : yi ≠ 0) (hj : yj ≠ 0) :
    edgeRes A Fi (-Fj / yi) (-Fi / yj) = -(Fi / (yi * yj)) * edgeRes A Fj yj yi ∧
      edgeRes A Fj (-Fi / yj) (-Fj / yi) = -(Fj / (yi * yj)) * edgeRes A Fi yi yj := by
  unfold edgeRes
  constructor <;> field_simp <;> ring

/-- For nonzero F_i,F_j, the edge map ι is an involution on pairs of nonzero messages. -/
theorem edgeInvolution_involutive {Fi Fj yi yj : K} (hFi : Fi ≠ 0) (hFj : Fj ≠ 0) (hi : yi ≠ 0)
    (hj : yj ≠ 0) : (-Fj / (-Fj / yi), -Fi / (-Fi / yj)) = (yi, yj) := by
  refine Prod.ext ?_ ?_ <;> field_simp

/-- At a dart with active tail, the chart edge equation is the edge residual R with
F=f_t=π_t w_t, y_i=q_α and y_j=q_ᾱ; on S the other branch y_α=−F_h/q_α is its involution. -/
theorem eval_chartEdge_eq_edgeRes (S : Finset E) (x : E ⊕ V → ℂ) (z : Dart E ⊕ V → ℂ)
    {α : Dart E} (ht : G.deg S (G.tail α) ≠ 0) :
    eval (Sum.elim x z) (G.chartEdge S α) = edgeRes (x (Sum.inl α.1))
      (x (Sum.inr (G.tail α)) * z (Sum.inr (G.tail α))) (z (Sum.inl α)) (z (Sum.inl (rev α))) := by
  simp only [chartEdge, ht, ↓reduceIte, vA, vP, vQ, vW, edgeRes, map_sub, map_mul, map_add,
    eval_X, Sum.elim_inl, Sum.elim_inr]
  ring

end EdgeInvolution

end Multigraph

end BPFixedPoints
