import BPFixedPoints.Degree.WeakCoupling.Branches

/-!
# Statewise charts at strong fields (`sf:normal-form`)

Fix a_e≠0,a_e²≠1 and study b_i→∞, p_i=b_i⁻¹→0. For a state S with no
degree-one vertices, put k_i=d_S(i), r_i=1 if k_i=0 and k_i−1 otherwise.
Unknowns are positive-branch messages q_α and normalized coordinates w_i,
with f_i=π_i w_i and F_i=f_i when active, f_i⁻¹ when inactive.
For parameters (a,π), π_i^{r_i}=(−1)^{k_i}p_i, define `chartSys` by:
inactive-tail edge equation q_α(1+aπ_t w_t q_ᾱ)−(a+π_t w_t q_ᾱ);
active-tail equation q_α(π_t w_t+aq_ᾱ)−(aπ_t w_t+q_ᾱ);
vertex equation w_i^{r_i}∏_{α→i,α∉S}q_α−∏_{α→i,α∈S}q_α.
At π=0, q⁰_α=a^{σ_t}, σ=+1 inactive and −1 active, with
ω_i^{r_i}=C_{S,i}(q⁰), gives a zero (`chartMap_base`). The unknown derivative
is triangular, with edge diagonal 1 or aq⁰_ᾱ and vertex diagonal
r_iω_i^{r_i−1}∏q⁰, hence invertible (`isInvertible_chartDeriv`).
The implicit function theorem gives continuous locally unique branches
(`exists_chart_branch`) for strong-field counting. The analytic coordinate
change to power-map normal form is `exists_powerMap_normal_form`. Admissibility for π≠0
is in `StrongField/ChartSolution.lean`.
-/

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

set_option linter.unusedSectionVars false

/-- Directional derivative Σ_j ∂_j p(x)d_j. -/
noncomputable def dirD (x d : σ → R) (p : MvPolynomial σ R) : R := ∑ j, eval x (pderiv j p) * d j

variable (x d : σ → R)

theorem dirD_add (p q : MvPolynomial σ R) : dirD x d (p + q) = dirD x d p + dirD x d q := by
  simp [dirD, add_mul, Finset.sum_add_distrib]

theorem dirD_sub (p q : MvPolynomial σ R) : dirD x d (p - q) = dirD x d p - dirD x d q := by
  simp [dirD, sub_mul, Finset.sum_sub_distrib]

theorem dirD_mul (p q : MvPolynomial σ R) :
    dirD x d (p * q) = dirD x d p * eval x q + eval x p * dirD x d q := by
  simp only [dirD, Derivation.leibniz, map_add, smul_eq_mul, eval_mul, add_mul,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring

theorem dirD_X (i : σ) : dirD x d (X i) = d i := by
  simp [dirD, pderiv_X, Pi.single_apply]

theorem dirD_C (c : R) : dirD x d (C c) = 0 := by
  simp [dirD]

theorem dirD_one : dirD x d (1 : MvPolynomial σ R) = 0 := by
  simp [dirD]

theorem dirD_pow (p : MvPolynomial σ R) (n : ℕ) :
    dirD x d (p ^ n) = n * eval x p ^ (n - 1) * dirD x d p := by
  induction n with
  | zero => simp [dirD_one]
  | succ n ih =>
    rw [pow_succ, dirD_mul, ih, eval_pow]
    cases n with
    | zero => simp
    | succ n =>
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      ring

theorem dirD_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → MvPolynomial σ R) :
    dirD x d (∏ γ ∈ s, f γ) = ∑ γ ∈ s, dirD x d (f γ) * ∏ δ ∈ s.erase γ, eval x (f δ) := by
  induction s using Finset.induction_on with
  | empty => simp [dirD_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, dirD_mul, ih, Finset.sum_insert ha, Finset.erase_insert ha]
    rw [eval_prod, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun γ hγ => ?_
    have hne : γ ≠ a := fun h => ha (h ▸ hγ)
    rw [Finset.erase_insert_of_ne hne.symm, Finset.prod_insert (by simp [ha])]
    ring

theorem gradCLM_eq_dirD {𝕜 : Type*} [NontriviallyNormedField 𝕜] (p : MvPolynomial σ 𝕜)
    (x d : σ → 𝕜) : p.gradCLM x d = dirD x d p := by
  rw [gradCLM_apply]; rfl

end MvPolynomial

namespace BPFixedPoints

set_option linter.unusedSectionVars false

open MvPolynomial Filter Topology

section ImplicitBranch

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [CompleteSpace E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Continuous branches by the implicit function theorem, with general parameter space.** -/
theorem exists_branch_of_hasStrictFDerivAt {f : E₁ × E₂ → F} {f' : E₁ × E₂ →L[𝕜] F}
    {u : E₁ × E₂} (hf : HasStrictFDerivAt f f' u)
    (hinv : (f'.comp (ContinuousLinearMap.inr 𝕜 E₁ E₂)).IsInvertible) :
    ∃ ψ : E₁ → E₂, ψ u.1 = u.2 ∧ (∀ᶠ x in 𝓝 u.1, ContinuousAt ψ x) ∧
      (∀ᶠ x in 𝓝 u.1, f (x, ψ x) = f u) ∧
      (∀ᶠ v in 𝓝 u, f v = f u → ψ v.1 = v.2) := by
  set ψ := hf.implicitFunctionOfProdDomain hinv
  set φ := hf.implicitFunctionDataOfProdDomain hinv
  have hψ : ∀ x, ψ x = (φ.toOpenPartialHomeomorph.symm (f u, x)).2 := fun x => rfl
  have hpt : φ.toOpenPartialHomeomorph φ.pt = (f u, u.1) := by
    rw [φ.toOpenPartialHomeomorph_apply]; rfl
  have htarget : (f u, u.1) ∈ φ.toOpenPartialHomeomorph.target := by
    rw [← hpt]; exact φ.map_pt_mem_toOpenPartialHomeomorph_target
  have hev := hf.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  refine ⟨ψ, ?_, ?_, hf.eventually_apply_implicitFunctionOfProdDomain hinv,
    hev.mono fun v hv h => hv.1 h⟩
  · have := hev.self_of_nhds
    exact this.1 rfl
  · have hW : ∀ᶠ x in 𝓝 u.1, (f u, x) ∈ φ.toOpenPartialHomeomorph.target := by
      have hc : Continuous fun x : E₁ => (f u, x) := continuous_const.prodMk continuous_id
      exact hc.continuousAt.eventually (φ.toOpenPartialHomeomorph.open_target.mem_nhds htarget)
    filter_upwards [hW] with x hx
    have h1 := (φ.toOpenPartialHomeomorph.continuousOn_symm.continuousAt
      (φ.toOpenPartialHomeomorph.open_target.mem_nhds hx))
    have h2 : ContinuousAt (fun x : E₁ => (f u, x)) x :=
      (continuous_const.prodMk continuous_id).continuousAt
    have := (h1.comp h2).snd
    have hfun : ψ = fun x => (φ.toOpenPartialHomeomorph.symm (f u, x)).2 := funext hψ
    rw [hfun]
    exact this

end ImplicitBranch

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Chart

/-- State: an edge set S with no vertex of S-degree one, hence contributing to Q. -/
def IsState (G : Multigraph V E) (S : Finset E) : Prop := ∀ i, G.deg S i ≠ 1

variable (S : Finset E)

/-- r_i=1 if k_i=0, and k_i−1 otherwise. -/
def rS (i : V) : ℕ := if G.deg S i = 0 then 1 else G.deg S i - 1

/-- Chart variables: parameters (a_e,π_i) and unknowns (q_α,w_i). -/
abbrev ChVar (V E : Type*) := (E ⊕ V) ⊕ (Dart E ⊕ V)

/-- Abbreviations for variables. -/
noncomputable def vA (e : E) : MvPolynomial (ChVar V E) ℂ := X (Sum.inl (Sum.inl e))
noncomputable def vP (i : V) : MvPolynomial (ChVar V E) ℂ := X (Sum.inl (Sum.inr i))
noncomputable def vQ (α : Dart E) : MvPolynomial (ChVar V E) ℂ := X (Sum.inr (Sum.inl α))
noncomputable def vW (i : V) : MvPolynomial (ChVar V E) ℂ := X (Sum.inr (Sum.inr i))

/-- Edge equation. -/
noncomputable def chartEdge (α : Dart E) : MvPolynomial (ChVar V E) ℂ :=
  if G.deg S (G.tail α) = 0 then
    vQ α * (1 + vA α.1 * vP (G.tail α) * vW (G.tail α) * vQ (rev α)) -
      (vA α.1 + vP (G.tail α) * vW (G.tail α) * vQ (rev α))
  else
    vQ α * (vP (G.tail α) * vW (G.tail α) + vA α.1 * vQ (rev α)) -
      (vA α.1 * vP (G.tail α) * vW (G.tail α) + vQ (rev α))

/-- Vertex equation. -/
noncomputable def chartVertex (i : V) : MvPolynomial (ChVar V E) ℂ :=
  vW i ^ G.rS S i * ∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∉ S), vQ α -
    ∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∈ S), vQ α

/-- Polynomial chart system. -/
noncomputable def chartSys : Dart E ⊕ V → MvPolynomial (ChVar V E) ℂ
  | Sum.inl α => G.chartEdge S α
  | Sum.inr i => G.chartVertex S i

/-- Linear map assembling parameter and unknown pairs into variable values. -/
noncomputable def chartL : ((E ⊕ V → ℂ) × (Dart E ⊕ V → ℂ)) →L[ℂ] (ChVar V E → ℂ) :=
  ContinuousLinearMap.pi fun j => match j with
    | Sum.inl k => (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.fst ℂ _ _)
    | Sum.inr k => (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.snd ℂ _ _)

theorem chartL_apply (v : (E ⊕ V → ℂ) × (Dart E ⊕ V → ℂ)) : chartL v = Sum.elim v.1 v.2 := by
  funext j; rcases j with k | k <;> rfl

/-- Chart map (a,π;q,w) to the polynomial-system values. -/
noncomputable def chartMap (v : (E ⊕ V → ℂ) × (Dart E ⊕ V → ℂ)) : Dart E ⊕ V → ℂ :=
  fun k => eval (Sum.elim v.1 v.2) (G.chartSys S k)

/-- Derivative of the chart map. -/
noncomputable def chartDeriv (v : (E ⊕ V → ℂ) × (Dart E ⊕ V → ℂ)) :
    ((E ⊕ V → ℂ) × (Dart E ⊕ V → ℂ)) →L[ℂ] (Dart E ⊕ V → ℂ) :=
  (ContinuousLinearMap.pi fun k => (G.chartSys S k).gradCLM (Sum.elim v.1 v.2)).comp chartL

theorem hasStrictFDerivAt_chartMap (v : (E ⊕ V → ℂ) × (Dart E ⊕ V → ℂ)) :
    HasStrictFDerivAt (G.chartMap S) (G.chartDeriv S v) v := by
  have h1 : HasStrictFDerivAt (fun x : ChVar V E → ℂ => fun k => eval x (G.chartSys S k))
      (ContinuousLinearMap.pi fun k => (G.chartSys S k).gradCLM (Sum.elim v.1 v.2))
      (Sum.elim v.1 v.2) :=
    hasStrictFDerivAt_pi.2 fun k => (G.chartSys S k).hasStrictFDerivAt_eval _
  have h2 : HasStrictFDerivAt (fun v : (E ⊕ V → ℂ) × (Dart E ⊕ V → ℂ) => Sum.elim v.1 v.2)
      (chartL (V := V) (E := E)) v := by
    have : (fun v : (E ⊕ V → ℂ) × (Dart E ⊕ V → ℂ) => Sum.elim v.1 v.2) = chartL := by
      funext v; rw [chartL_apply]
    rw [this]; exact chartL.hasStrictFDerivAt
  exact h1.comp v h2

theorem chartDeriv_inr_apply (v : (E ⊕ V → ℂ) × (Dart E ⊕ V → ℂ)) (δ : Dart E ⊕ V → ℂ)
    (k : Dart E ⊕ V) :
    G.chartDeriv S v (0, δ) k = dirD (Sum.elim v.1 v.2) (Sum.elim 0 δ) (G.chartSys S k) := by
  simp only [chartDeriv, ContinuousLinearMap.comp_apply, chartL_apply,
    ContinuousLinearMap.pi_apply, gradCLM_eq_dirD]

/-! ### Base point -/

variable (a : E → ℂ) (ω : V → ℂ)

/-- Positive-branch message q⁰_α=a^{σ_t} at π=0. -/
noncomputable def q0 (α : Dart E) : ℂ := if G.deg S (G.tail α) = 0 then a α.1 else (a α.1)⁻¹

/-- C_{S,i}(q⁰) = ∏_{α∈S} q⁰ / ∏_{α∉S} q⁰。 -/
noncomputable def C0 (i : V) : ℂ :=
  (∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∈ S), G.q0 S a α) /
    ∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∉ S), G.q0 S a α

/-- Base point ((a,0),(q⁰,ω)). -/
noncomputable def basePt : (E ⊕ V → ℂ) × (Dart E ⊕ V → ℂ) :=
  (Sum.elim a 0, Sum.elim (G.q0 S a) ω)

variable {G S a ω}

theorem q0_ne_zero (ha : ∀ e, a e ≠ 0) (α : Dart E) : G.q0 S a α ≠ 0 := by
  unfold q0; split_ifs <;> simp [ha]

theorem C0_ne_zero (ha : ∀ e, a e ≠ 0) (i : V) : G.C0 S a i ≠ 0 := by
  unfold C0
  exact div_ne_zero (Finset.prod_ne_zero_iff.2 fun α _ => q0_ne_zero ha α)
    (Finset.prod_ne_zero_iff.2 fun α _ => q0_ne_zero ha α)

/-- The base point is a zero of the chart system. -/
theorem chartMap_base (ha : ∀ e, a e ≠ 0) (hω : ∀ i, ω i ^ G.rS S i = G.C0 S a i) :
    G.chartMap S (G.basePt S a ω) = 0 := by
  funext k
  rcases k with α | i
  · simp only [chartMap, chartSys, chartEdge, basePt, vA, vP, vQ, vW, Pi.zero_apply]
    split_ifs with h
    · simp [q0, h]
    · simp only [map_sub, map_mul, map_add, eval_X, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
        zero_mul, zero_add, mul_zero]
      have hq : G.q0 S a α = (a α.1)⁻¹ := by simp [q0, h]
      rw [hq]
      field_simp [ha α.1]
      ring
  · simp only [chartMap, chartSys, chartVertex, basePt, vQ, vW, map_sub, map_mul, map_pow,
      map_prod, eval_X, Sum.elim_inr, Sum.elim_inl, Pi.zero_apply]
    rw [hω i, C0, div_mul_cancel₀ _ (Finset.prod_ne_zero_iff.2 fun α _ => q0_ne_zero ha α),
      sub_self]

/-- The unknown derivative at the base point has trivial kernel. -/
theorem chartDeriv_base_inj (hS : IsState G S) (ha : ∀ e, a e ≠ 0) (hω0 : ∀ i, ω i ≠ 0)
    (δ : Dart E ⊕ V → ℂ)
    (hδ : G.chartDeriv S (G.basePt S a ω) (0, δ) = 0) : δ = 0 := by
  have hrow : ∀ k, dirD (Sum.elim (Sum.elim a 0) (Sum.elim (G.q0 S a) ω)) (Sum.elim 0 δ)
      (G.chartSys S k) = 0 := fun k => by
    have := congrFun hδ k
    rwa [chartDeriv_inr_apply] at this
  set x := Sum.elim (Sum.elim a 0) (Sum.elim (G.q0 S a) ω)
  set d : ChVar V E → ℂ := Sum.elim 0 δ
  have dA : ∀ e, dirD x d (vA (V := V) e) = 0 := fun e => by simp [vA, dirD_X, d]
  have dP : ∀ i, dirD x d (vP (E := E) i) = 0 := fun i => by simp [vP, dirD_X, d]
  have dQ : ∀ α, dirD x d (vQ (V := V) α) = δ (Sum.inl α) := fun α => by simp [vQ, dirD_X, d]
  have dW : ∀ i, dirD x d (vW (E := E) i) = δ (Sum.inr i) := fun i => by simp [vW, dirD_X, d]
  have eP : ∀ i, eval x (vP (E := E) i) = 0 := fun i => by simp [vP, x]
  have eA : ∀ e, eval x (vA (V := V) e) = a e := fun e => by simp [vA, x]
  have eQ : ∀ α, eval x (vQ (V := V) α) = G.q0 S a α := fun α => by simp [vQ, x]
  -- Edge rows imply δq=0.
  have hq : ∀ α, δ (Sum.inl α) = 0 := by
    intro α
    have h := hrow (Sum.inl α)
    simp only [chartSys, chartEdge] at h
    split_ifs at h with ht
    · simp only [dirD_sub, dirD_mul, dirD_add, dirD_one, dA, dP, dQ, dW, eP, eA, eQ, map_add,
        map_mul, map_one, mul_zero, zero_mul, add_zero, mul_one, sub_zero] at h
      exact h
    · simp only [dirD_sub, dirD_mul, dirD_add, dA, dP, dQ, dW, eP, eA, eQ, map_add, map_mul,
        mul_zero, zero_mul, add_zero, zero_add] at h
      have hq0 : G.q0 S a α = (a α.1)⁻¹ := by simp [q0, ht]
      rw [hq0] at h
      have e1 : (a α.1)⁻¹ * (a α.1 * δ (Sum.inl (rev α))) = δ (Sum.inl (rev α)) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ha α.1), one_mul]
      have hne : a α.1 * G.q0 S a (rev α) ≠ 0 := mul_ne_zero (ha α.1) (q0_ne_zero ha _)
      have : δ (Sum.inl α) * (a α.1 * G.q0 S a (rev α)) = 0 := by linear_combination h - e1
      exact (mul_eq_zero.1 this).resolve_right hne
  -- Vertex rows imply δw=0.
  have hw : ∀ i, δ (Sum.inr i) = 0 := by
    intro i
    have h := hrow (Sum.inr i)
    simp only [chartSys, chartVertex, dirD_sub, dirD_mul, dirD_pow, dirD_prod, dQ, dW, hq,
      zero_mul, Finset.sum_const_zero, mul_zero, add_zero, sub_zero] at h
    have hpos : (G.rS S i : ℂ) ≠ 0 := by
      have := hS i
      unfold rS; split_ifs <;> [simp; exact Nat.cast_ne_zero.2 (by omega)]
    have hprod : eval x (∏ α ∈ (G.inDarts i).filter (fun α => α.1 ∉ S), vQ (V := V) α) ≠ 0 := by
      rw [eval_prod]; exact Finset.prod_ne_zero_iff.2 fun α _ => by rw [eQ]; exact q0_ne_zero ha α
    have hw0 : eval x (vW (E := E) i) ≠ 0 := by simp [vW, x, hω0 i]
    rcases mul_eq_zero.1 h with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · rcases mul_eq_zero.1 h2 with h3 | h3
        · exact absurd h3 hpos
        · exact absurd (eq_zero_of_pow_eq_zero h3) hw0
      · exact h2
    · exact absurd h1 hprod
  funext k
  rcases k with α | i
  · exact hq α
  · exact hw i

/-- The unknown derivative at the base point is invertible. -/
theorem isInvertible_chartDeriv (hS : IsState G S) (ha : ∀ e, a e ≠ 0) (hω0 : ∀ i, ω i ≠ 0) :
    ((G.chartDeriv S (G.basePt S a ω)).comp
      (ContinuousLinearMap.inr ℂ (E ⊕ V → ℂ) (Dart E ⊕ V → ℂ))).IsInvertible := by
  set T := (G.chartDeriv S (G.basePt S a ω)).comp
    (ContinuousLinearMap.inr ℂ (E ⊕ V → ℂ) (Dart E ⊕ V → ℂ))
  have hinj : Function.Injective T.toLinearMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro δ hδ
    exact chartDeriv_base_inj hS ha hω0 δ hδ
  let e := (LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  ext δ
  simp [e, LinearEquiv.coe_ofInjectiveEndo]

/-- **Statewise chart branches by the implicit function theorem.** Near (a,π)=(a⁰,0) there is a continuous solution ψ with ψ(a⁰,0)=(q⁰,ω), and it is the unique nearby solution. -/
theorem exists_chart_branch (hS : IsState G S) (ha : ∀ e, a e ≠ 0)
    (hω : ∀ i, ω i ^ G.rS S i = G.C0 S a i)
    (hω0 : ∀ i, ω i ≠ 0) :
    ∃ ψ : (E ⊕ V → ℂ) → (Dart E ⊕ V → ℂ), ψ (Sum.elim a 0) = Sum.elim (G.q0 S a) ω ∧
      (∀ᶠ x in 𝓝 (Sum.elim a 0), ContinuousAt ψ x) ∧
      (∀ᶠ x in 𝓝 (Sum.elim a 0), G.chartMap S (x, ψ x) = 0) ∧
      (∀ᶠ v in 𝓝 (G.basePt S a ω), G.chartMap S v = 0 → ψ v.1 = v.2) := by
  obtain ⟨ψ, h1, h2, h3, h4⟩ := exists_branch_of_hasStrictFDerivAt
    (G.hasStrictFDerivAt_chartMap S (G.basePt S a ω)) (isInvertible_chartDeriv hS ha hω0)
  rw [chartMap_base ha hω] at h3 h4
  exact ⟨ψ, h1, h2, h3, h4⟩

end Chart

end Multigraph

end BPFixedPoints
