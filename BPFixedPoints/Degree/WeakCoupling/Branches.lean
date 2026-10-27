import BPFixedPoints.Degree.WeakCoupling.Line
import BPFixedPoints.Degree.Limit.Real
import BPFixedPoints.Degree.PolynomialDerivative

/-!
# Weak-coupling branch convergence and real-root counts

View the auxiliary system along s_e=1+εc_e, fixed c_e≠0 and β_i≠0,−1, as
`weakMap (ε,z)`. At ε=0 it is `limitSystem₀`, whose z-Jacobian is invertible
at each limit point (`jacLimit_mulVec_eq_zero`).

* `MvPolynomial.hasStrictFDerivAt_eval` gives the strict derivative of evaluation
  as Σ_j(∂_j p)(x)·proj_j. Thus `weakMap` is strictly differentiable at (0,x)
  with the limit Jacobian as z-derivative (`hasStrictFDerivAt_weakMap`,
  `weakDeriv_comp_inr`, `isInvertible_weakDeriv_comp_inr`).
* The implicit function theorem `HasStrictFDerivAt.implicitFunctionOfProdDomain`
  gives a unique local branch converging to each limit point (`exists_local_branch`).
  Its points are admissible for ε≠0 (`exists_isAuxSolution_of_near`): edge
  equations and εc_e≠0 exclude active coordinates A=−1.
* `weak_coupling_master` gives one solution near each limit point and puts every
  solution in one such neighborhood, for sufficiently small η and ε≠0. Distinct
  branches give Q solutions and exhaust the count `card_weak_coupling_eq_Q`.
* For real c_e≠0, β_i>0 and small real t≠0, `card_real_weak_coupling` identifies
  the number of real auxiliary solutions with real limit points; connected
  graphs give 2^ν (`card_real_weak_coupling_of_connected`). Conjugation and local
  uniqueness make real branches real; separation of limit points by 2η₀ excludes
  real points on nonreal branches. Use `realAuxEquiv` and `realLimitEquiv`.

The BP count for a_e²=1+t c_e, b_i=β_i∏_{e∋i}a_e follows from `admissibleEquivAux`
(`card_real_admissible_weak_coupling`), and is 2^ν if connected.
Only each fixed line (c,β) is treated. Uniformity in a whole real neighborhood
of (a,b)=(1,b⁰), positive/stable solutions and real-root BP indices are not treated here.
-/


namespace BPFixedPoints

set_option linter.unusedSectionVars false

section LocalBranch

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

open Filter Topology

/--
Local branch from the implicit function theorem: if f(0,x₀)=0 and the
z-derivative is invertible, a branch ψ tends to x₀, solves f(ε,ψ ε)=0
for small ε, and is the unique zero in some fixed ball around x₀.
-/
theorem exists_local_branch {f : 𝕜 × E₂ → F} {f' : 𝕜 × E₂ →L[𝕜] F} {x₀ : E₂}
    (hf : HasStrictFDerivAt f f' ((0 : 𝕜), x₀)) (h0 : f ((0 : 𝕜), x₀) = 0)
    (hinv : (f'.comp (ContinuousLinearMap.inr 𝕜 𝕜 E₂)).IsInvertible) :
    ∃ r > 0, ∃ ψ : 𝕜 → E₂, (∀ δ > 0, ∃ ε₁ > 0, ∀ ε : 𝕜, ‖ε‖ < ε₁ → ‖ψ ε - x₀‖ < δ) ∧
      ∃ ε₀ > 0, ∀ ε : 𝕜, ‖ε‖ < ε₀ →
        f (ε, ψ ε) = 0 ∧ ∀ z : E₂, ‖z - x₀‖ < r → f (ε, z) = 0 → z = ψ ε := by
  set ψ := hf.implicitFunctionOfProdDomain hinv
  have h1 := hf.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  have h2 := hf.tendsto_implicitFunctionOfProdDomain hinv
  rw [h0] at h1
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 h1
  have hψ : ∀ δ > 0, ∃ ε₁ > 0, ∀ ε : 𝕜, ‖ε‖ < ε₁ → ‖ψ ε - x₀‖ < δ := by
    intro δ hδ
    obtain ⟨ε₁, hε₁, h⟩ := Metric.tendsto_nhds_nhds.1 h2 δ hδ
    refine ⟨ε₁, hε₁, fun ε hε => ?_⟩
    have := h (by simpa [dist_eq_norm] using hε)
    simpa [dist_eq_norm] using this
  refine ⟨ρ, hρ, ψ, hψ, ?_⟩
  obtain ⟨ε₁, hε₁, hε₁'⟩ := hψ ρ hρ
  refine ⟨min ρ ε₁, lt_min hρ hε₁, fun ε hε => ⟨?_, fun z hz hfz => ?_⟩⟩
  · have hd : dist (ε, ψ ε) ((0 : 𝕜), x₀) < ρ := by
      rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm, sub_zero]
      exact ⟨lt_of_lt_of_le hε (min_le_left _ _), hε₁' ε (lt_of_lt_of_le hε (min_le_right _ _))⟩
    exact (hball hd).2 rfl
  · have hd : dist (ε, z) ((0 : 𝕜), x₀) < ρ := by
      rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm, sub_zero]
      exact ⟨lt_of_lt_of_le hε (min_le_left _ _), hz⟩
    exact ((hball hd).1 hfz).symm

omit [CompleteSpace 𝕜] in
/-- Positive lower bound for finitely many positive numbers. -/
theorem exists_pos_forall_le {ι : Type*} [Fintype ι] (g : ι → ℝ) (hg : ∀ i, 0 < g i) :
    ∃ δ > 0, ∀ i, δ ≤ g i := by
  classical
  let T : Finset ℝ := insert 1 (Finset.univ.image g)
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  refine ⟨T.min' hT, ?_, fun i => T.min'_le _ (Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem g (Finset.mem_univ i)))⟩
  show 0 < T.min' hT
  rw [Finset.lt_min'_iff]
  intro y hy
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact one_pos
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hy
    exact hg i

end LocalBranch

namespace Multigraph

open BP MvPolynomial

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [DecidableEq 𝕜]

/-- Weak-coupling auxiliary family s_e=1+ε c_e as a map of (ε,z). -/
noncomputable def weakMap (c : E → 𝕜) (β : V → 𝕜) (q : 𝕜 × (Var V E → 𝕜)) : Var V E → 𝕜 :=
  fun v => eval q.2 (G.auxSystem (fun e => 1 + q.1 * c e) β v)

/-- Perturbation term c_e A_α A_revα, absent from the vertex equations. -/
noncomputable def pertPoly (c : E → 𝕜) : Var V E → MvPolynomial (Var V E) 𝕜
  | Sum.inl α => C (c α.1) * X (Sum.inl α) * X (Sum.inl (rev α))
  | Sum.inr _ => 0

theorem auxSystem_one_eq_limitSystem₀ (c : E → 𝕜) (β : V → 𝕜) (v : Var V E) :
    G.auxSystem (fun _ => 1) β v = G.limitSystem₀ c β v := by
  cases v with
  | inl α => simp [auxSystem, limitSystem₀, auxEdgePoly, edgePoly]; ring
  | inr i => rfl

theorem weakMap_eq (c : E → 𝕜) (β : V → 𝕜) (q : 𝕜 × (Var V E → 𝕜)) :
    G.weakMap c β q =
      (fun v => eval q.2 (G.limitSystem₀ c β v)) + q.1 • fun v => eval q.2 (pertPoly c v) := by
  ext v
  cases v with
  | inl α =>
    simp [weakMap, ← auxSystem_one_eq_limitSystem₀, auxSystem, auxEdgePoly, pertPoly]; ring
  | inr i => simp [weakMap, limitSystem₀, auxSystem, pertPoly]

/-- Continuous linear map of the limit-system Jacobian. -/
noncomputable def jacCLM (c : E → 𝕜) (β : V → 𝕜) (x : Var V E → 𝕜) :
    (Var V E → 𝕜) →L[𝕜] (Var V E → 𝕜) :=
  ContinuousLinearMap.pi fun v => (G.limitSystem₀ c β v).gradCLM x

theorem jacCLM_apply (c : E → 𝕜) (β : V → 𝕜) (x w : Var V E → 𝕜) :
    G.jacCLM c β x w = (G.jacLimit c β x).mulVec w := by
  ext v
  rw [jacLimit_mulVec]
  simp [jacCLM, gradCLM_apply]

theorem hasStrictFDerivAt_limitMap (c : E → 𝕜) (β : V → 𝕜) (x : Var V E → 𝕜) :
    HasStrictFDerivAt (fun z : Var V E → 𝕜 => fun v => eval z (G.limitSystem₀ c β v))
      (G.jacCLM c β x) x :=
  hasStrictFDerivAt_pi.2 fun v => (G.limitSystem₀ c β v).hasStrictFDerivAt_eval x

/-- Gradient of the perturbation term. -/
noncomputable def pertCLM (c : E → 𝕜) (x : Var V E → 𝕜) :
    (Var V E → 𝕜) →L[𝕜] (Var V E → 𝕜) :=
  ContinuousLinearMap.pi fun v => (pertPoly c v).gradCLM x

/-- Strong derivative of the weak-coupling map at (0,x). -/
noncomputable def weakDeriv (c : E → 𝕜) (β : V → 𝕜) (x : Var V E → 𝕜) :
    𝕜 × (Var V E → 𝕜) →L[𝕜] (Var V E → 𝕜) :=
  (G.jacCLM c β x).comp (ContinuousLinearMap.snd 𝕜 𝕜 (Var V E → 𝕜)) +
    (ContinuousLinearMap.fst 𝕜 𝕜 (Var V E → 𝕜)).smulRight fun v => eval x (pertPoly c v)

theorem hasStrictFDerivAt_weakMap (c : E → 𝕜) (β : V → 𝕜) (x : Var V E → 𝕜) :
    HasStrictFDerivAt (G.weakMap c β) (G.weakDeriv c β x) (0, x) := by
  have hg : HasStrictFDerivAt
      (fun q : 𝕜 × (Var V E → 𝕜) => fun v => eval q.2 (G.limitSystem₀ c β v))
      ((G.jacCLM c β x).comp (ContinuousLinearMap.snd 𝕜 𝕜 (Var V E → 𝕜))) (0, x) := by
    have h1 := G.hasStrictFDerivAt_limitMap c β x
    have h2 : HasStrictFDerivAt (Prod.snd : 𝕜 × (Var V E → 𝕜) → Var V E → 𝕜)
        (ContinuousLinearMap.snd 𝕜 𝕜 (Var V E → 𝕜)) ((0 : 𝕜), x) := hasStrictFDerivAt_snd
    exact h1.comp ((0 : 𝕜), x) h2
  have hh : HasStrictFDerivAt
      (fun q : 𝕜 × (Var V E → 𝕜) => fun v => eval q.2 (pertPoly c v))
      ((pertCLM c x).comp (ContinuousLinearMap.snd 𝕜 𝕜 (Var V E → 𝕜))) (0, x) := by
    have h1 : HasStrictFDerivAt (fun z : Var V E → 𝕜 => fun v => eval z (pertPoly c v))
        (pertCLM c x) x :=
      hasStrictFDerivAt_pi.2 fun v => (pertPoly c v).hasStrictFDerivAt_eval x
    have h2 : HasStrictFDerivAt (Prod.snd : 𝕜 × (Var V E → 𝕜) → Var V E → 𝕜)
        (ContinuousLinearMap.snd 𝕜 𝕜 (Var V E → 𝕜)) ((0 : 𝕜), x) := hasStrictFDerivAt_snd
    exact h1.comp ((0 : 𝕜), x) h2
  have hs := hasStrictFDerivAt_fst.smul hh
  have hsum := hg.add hs
  have hf : G.weakMap c β = (fun q : 𝕜 × (Var V E → 𝕜) => fun v => eval q.2 (G.limitSystem₀ c β v)) +
      fun q => q.1 • fun v => eval q.2 (pertPoly c v) := by
    funext q; rw [weakMap_eq]; rfl
  rw [hf]
  convert hsum using 1
  simp [weakDeriv]

theorem weakDeriv_comp_inr (c : E → 𝕜) (β : V → 𝕜) (x : Var V E → 𝕜) :
    (G.weakDeriv c β x).comp (ContinuousLinearMap.inr 𝕜 𝕜 (Var V E → 𝕜)) = G.jacCLM c β x := by
  ext w
  simp [weakDeriv]

/-- At a limit point the partial z-derivative is invertible. -/
theorem isInvertible_weakDeriv_comp_inr [CharZero 𝕜] [CompleteSpace 𝕜] {c : E → 𝕜} {β : V → 𝕜}
    (hβ1 : ∀ i, β i ≠ -1) {S : Finset E} {F : V → 𝕜}
    (hF : ∀ i, VertexLimitEq (G.deg S i) (β i) (F i)) :
    ((G.weakDeriv c β (G.limitPoint S F)).comp
      (ContinuousLinearMap.inr 𝕜 𝕜 (Var V E → 𝕜))).IsInvertible := by
  rw [weakDeriv_comp_inr]
  have hinj : Function.Injective (G.jacCLM c β (G.limitPoint S F)).toLinearMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply G.jacLimit_mulVec_eq_zero hβ1 hF
    rw [← jacCLM_apply]
    exact hw
  let e := (LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  ext w
  simp [e, LinearEquiv.coe_ofInjectiveEndo]

theorem weakMap_zero (c : E → 𝕜) (β : V → 𝕜) (x : Var V E → 𝕜) :
    G.weakMap c β ((0 : 𝕜), x) = fun v => eval x (G.limitSystem₀ c β v) := by
  rw [weakMap_eq]; simp

/-- Near a limit point, a family zero with ε≠0 is automatically an admissible auxiliary solution. -/
theorem exists_isAuxSolution_of_near [CharZero 𝕜] {c : E → 𝕜} (hc : ∀ e, c e ≠ 0) {β : V → 𝕜}
    (hβ1 : ∀ i, β i ≠ -1) {S : Finset E} {F : V → 𝕜}
    (hF : ∀ i, VertexLimitEq (G.deg S i) (β i) (F i)) :
    ∃ δ > 0, ∀ ε : 𝕜, ε ≠ 0 → ∀ z : Var V E → 𝕜, ‖z - G.limitPoint S F‖ < δ →
      G.weakMap c β (ε, z) = 0 →
        G.IsAuxSolution (fun e => 1 + ε * c e) β (fun α => z (Sum.inl α)) (fun i => z (Sum.inr i)) := by
  set x₀ := G.limitPoint S F
  have hL := G.isLimitSolution_limitCoords hβ1 hF
  have hx0 : ∀ v, x₀ v ≠ 0 := by
    rintro (α | i)
    · simp only [x₀, limitPoint, limitCoords]
      split_ifs
      · norm_num
      · exact hL.ne_zero _
    · exact hL.ne_zero i
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_forall_le
    (fun v => min ‖x₀ v‖ (if x₀ v = -1 then 1 else ‖x₀ v + 1‖)) (fun v => by
      refine lt_min (norm_pos_iff.2 (hx0 v)) ?_
      split_ifs with h
      · exact one_pos
      · exact norm_pos_iff.2 fun h' => h (eq_neg_of_add_eq_zero_left h'))
  refine ⟨δ, hδ, fun ε hε z hz hfz => ?_⟩
  have hcoord : ∀ v, ‖z v - x₀ v‖ < δ := fun v =>
    lt_of_le_of_lt (norm_le_pi_norm (z - x₀) v) hz
  have hz0 : ∀ v, z v ≠ 0 := by
    intro v h0
    have h1 := hcoord v
    have h2 := (hδle v).trans (min_le_left _ _)
    rw [h0, zero_sub, norm_neg] at h1
    linarith
  have hz1 : ∀ v, x₀ v ≠ -1 → z v ≠ -1 := by
    intro v hv h0
    have h1 := hcoord v
    have h2 := (hδle v).trans (min_le_right _ _)
    simp only [hv, ↓reduceIte] at h2
    rw [h0, show (-1 : 𝕜) - x₀ v = -(x₀ v + 1) by ring, norm_neg] at h1
    linarith
  have hsys : ∀ v, eval z (G.auxSystem (fun e => 1 + ε * c e) β v) = 0 := fun v =>
    congrFun hfz v
  rw [← isAuxSolution_iff, eval_auxDen_ne_zero_iff]
  refine ⟨hsys, fun α => hz0 _, fun α => ?_, fun i => hz0 _, fun i => hz1 _ (hL.ne_neg_one i)⟩
  by_cases hα : x₀ (Sum.inl α) = -1
  · intro hA
    have he := hsys (Sum.inl (rev α))
    simp only [auxSystem, eval_auxEdgePoly, rev_rev, hA] at he
    have : -(ε * c (rev α).1) * z (Sum.inl (rev α)) = 0 := by linear_combination he
    rcases mul_eq_zero.1 this with h | h
    · exact mul_ne_zero hε (hc _) (neg_eq_zero.1 h)
    · exact hz0 _ h
  · exact hz1 _ hα


section Transfer

variable {G}
variable {K L : Type*} [Field K] [Field L] (φ : K →+* L)

theorem IsAuxSolution.map {s : E → K} {β : V → K} {A : Dart E → K} {F : V → K}
    (h : G.IsAuxSolution s β A F) : G.IsAuxSolution (φ ∘ s) (φ ∘ β) (φ ∘ A) (φ ∘ F) where
  A_ne_zero α := by simpa using h.A_ne_zero α
  A_ne_neg_one α := by
    intro h'; apply h.A_ne_neg_one α; apply φ.injective; simpa using h'
  F_ne_zero i := by simpa using h.F_ne_zero i
  F_ne_neg_one i := by
    intro h'; apply h.F_ne_neg_one i; apply φ.injective; simpa using h'
  edge α := by
    have := congrArg φ (h.edge α); simpa [map_mul, map_add] using this
  vertex i := by
    have := congrArg φ (h.vertex i); simpa [map_mul, map_zpow₀, map_prod] using this

theorem IsAuxSolution.of_map {s : E → K} {β : V → K} {A : Dart E → K} {F : V → K}
    (h : G.IsAuxSolution (φ ∘ s) (φ ∘ β) (φ ∘ A) (φ ∘ F)) : G.IsAuxSolution s β A F where
  A_ne_zero α := by intro h'; apply h.A_ne_zero α; simp [h']
  A_ne_neg_one α := by intro h'; apply h.A_ne_neg_one α; simp [h']
  F_ne_zero i := by intro h'; apply h.F_ne_zero i; simp [h']
  F_ne_neg_one i := by intro h'; apply h.F_ne_neg_one i; simp [h']
  edge α := by
    apply φ.injective; simpa [map_mul, map_add] using h.edge α
  vertex i := by
    apply φ.injective; simpa [map_mul, map_zpow₀, map_prod] using h.vertex i

theorem IsLimitSolution.map {β : V → K} {A : Dart E → K} {F : V → K}
    (h : G.IsLimitSolution β A F) : G.IsLimitSolution (φ ∘ β) (φ ∘ A) (φ ∘ F) where
  ne_zero i := by simpa using h.ne_zero i
  ne_neg_one i := by
    intro h'; apply h.ne_neg_one i; apply φ.injective; simpa using h'
  edge α := by
    have := congrArg φ (h.edge α); simpa [map_mul, map_add, map_sub] using this
  vertex i := by
    have := congrArg φ (h.vertex i); simpa [map_mul, map_zpow₀, map_prod] using this

theorem IsLimitSolution.of_map {β : V → K} {A : Dart E → K} {F : V → K}
    (h : G.IsLimitSolution (φ ∘ β) (φ ∘ A) (φ ∘ F)) : G.IsLimitSolution β A F where
  ne_zero i := by intro h'; apply h.ne_zero i; simp [h']
  ne_neg_one i := by intro h'; apply h.ne_neg_one i; simp [h']
  edge α := by
    apply φ.injective; simpa [map_mul, map_add, map_sub] using h.edge α
  vertex i := by
    apply φ.injective; simpa [map_mul, map_zpow₀, map_prod] using h.vertex i

end Transfer

section Complex

/-- Arrange a limit solution as a point Var V E→K. -/
def limPt {K : Type*} [Field K] {β : V → K} (p : G.LimitSolutions β) : Var V E → K :=
  Sum.elim p.1.1 p.1.2

theorem limPt_eq_limitPoint {K : Type*} [Field K] [DecidableEq K] {β : V → K}
    (p : G.LimitSolutions β) :
    G.limPt p = G.limitPoint (activeSet p.1.1) p.1.2 := by
  funext v
  rcases v with α | i
  · simp only [limPt, Sum.elim_inl, limitPoint]
    exact congrFun p.2.eq_limitCoords α
  · rfl

theorem limPt_injective {K : Type*} [Field K] {β : V → K} :
    Function.Injective (G.limPt (β := β)) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext
  · funext α; exact congrFun h (Sum.inl α)
  · funext i; exact congrFun h (Sum.inr i)

/-- Auxiliary solution in point form. -/
def IsAuxPt {K : Type*} [Field K] (s : E → K) (β : V → K) (z : Var V E → K) : Prop :=
  G.IsAuxSolution s β (fun α => z (Sum.inl α)) (fun i => z (Sum.inr i))

/-- **Weak-coupling branches.** For sufficiently small η and ε≠0, exactly one auxiliary solution lies within η of each limit point and all solutions lie in these neighborhoods. Distinct limit points are separated by at least 2η₀. -/
theorem weak_coupling_master (c : E → ℂ) (hc : ∀ e, c e ≠ 0) (β : V → ℂ) (hβ0 : ∀ i, β i ≠ 0)
    (hβ1 : ∀ i, β i ≠ -1) :
    ∃ η₀ > 0, (∀ p q : G.LimitSolutions β, ‖G.limPt p - G.limPt q‖ < 2 * η₀ → p = q) ∧
      ∀ η, 0 < η → η ≤ η₀ → ∃ ε₀ > 0, ∀ ε : ℂ, ε ≠ 0 → ‖ε‖ < ε₀ →
        (∀ z, G.IsAuxPt (fun e => 1 + ε * c e) β z → ∃ p : G.LimitSolutions β, ‖z - G.limPt p‖ < η) ∧
        (∀ p : G.LimitSolutions β, ∃ z, G.IsAuxPt (fun e => 1 + ε * c e) β z ∧ ‖z - G.limPt p‖ < η) ∧
        (∀ (p : G.LimitSolutions β) z z', G.IsAuxPt (fun e => 1 + ε * c e) β z → G.IsAuxPt (fun e => 1 + ε * c e) β z' →
          ‖z - G.limPt p‖ < η₀ → ‖z' - G.limPt p‖ < η₀ → z = z') := by
  classical
  have hcard := G.card_limitSolutions β hβ0 hβ1
  have : Finite (G.LimitSolutions β) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact G.Q_pos.ne')
  have : Fintype (G.LimitSolutions β) := Fintype.ofFinite _
  -- Local branch at each limit point.
  have hbranch : ∀ p : G.LimitSolutions β, ∃ r > 0, ∃ ψ : ℂ → (Var V E → ℂ),
      (∀ δ > 0, ∃ ε₁ > 0, ∀ ε : ℂ, ‖ε‖ < ε₁ → ‖ψ ε - G.limPt p‖ < δ) ∧
      ∃ ε₀ > 0, ∀ ε : ℂ, ‖ε‖ < ε₀ → G.weakMap c β (ε, ψ ε) = 0 ∧
        ∀ z, ‖z - G.limPt p‖ < r → G.weakMap c β (ε, z) = 0 → z = ψ ε := by
    intro p
    rw [limPt_eq_limitPoint]
    have hF := p.2.vertexLimitEq
    refine exists_local_branch (G.hasStrictFDerivAt_weakMap c β _) ?_
      (G.isInvertible_weakDeriv_comp_inr hβ1 hF)
    rw [weakMap_zero]
    funext v
    exact G.eval_limitSystem₀_limitPoint hβ1 hF v
  choose r hr ψ hψ ε₀b hε₀b hεb using hbranch
  have hnear : ∀ p : G.LimitSolutions β, ∃ δ > 0, ∀ ε : ℂ, ε ≠ 0 → ∀ z : Var V E → ℂ,
      ‖z - G.limPt p‖ < δ → G.weakMap c β (ε, z) = 0 → G.IsAuxPt (fun e => 1 + ε * c e) β z := by
    intro p
    rw [limPt_eq_limitPoint]
    exact G.exists_isAuxSolution_of_near hc hβ1 p.2.vertexLimitEq
  choose δn hδn hδnear using hnear
  -- Separation.
  obtain ⟨sep, hsep, hsep_le⟩ := exists_pos_forall_le
    (fun pq : G.LimitSolutions β × G.LimitSolutions β =>
      if pq.1 = pq.2 then 1 else ‖G.limPt pq.1 - G.limPt pq.2‖)
    (fun pq => by
      split_ifs with h
      · exact one_pos
      · exact norm_pos_iff.2 (sub_ne_zero.2 fun h' => h (G.limPt_injective h')))
  obtain ⟨η₁, hη₁, hη₁le⟩ := exists_pos_forall_le (fun p => min (r p) (δn p))
    (fun p => lt_min (hr p) (hδn p))
  have hsepP : ∀ p q : G.LimitSolutions β,
      ‖G.limPt p - G.limPt q‖ < 2 * min η₁ (sep / 2) → p = q := by
    intro p q hpq
    by_contra hne
    have h1 := hsep_le (p, q)
    simp only [hne, ↓reduceIte] at h1
    have h2 : 2 * min η₁ (sep / 2) ≤ sep := by
      have := min_le_right η₁ (sep / 2); linarith
    linarith
  refine ⟨min η₁ (sep / 2), lt_min hη₁ (half_pos hsep), hsepP, ?_⟩
  · intro η hη hηle
    have hη₀r : ∀ p, min η₁ (sep / 2) ≤ r p := fun p =>
      (min_le_left _ _).trans ((hη₁le p).trans (min_le_left _ _))
    have hη₀δ : ∀ p, min η₁ (sep / 2) ≤ δn p := fun p =>
      (min_le_left _ _).trans ((hη₁le p).trans (min_le_right _ _))
    choose ε₁ hε₁ hε₁' using fun p => hψ p η hη
    obtain ⟨εQ, hεQ, hQ⟩ := G.card_weak_coupling_eq_Q c hc β hβ0 hβ1
    obtain ⟨ε₀, hε₀, hε₀le⟩ := exists_pos_forall_le
      (fun pk : G.LimitSolutions β × Fin 3 => match pk.2 with
        | 0 => ε₀b pk.1 | 1 => ε₁ pk.1 | 2 => εQ)
      (fun pk => by
        rcases pk with ⟨p, k⟩
        fin_cases k
        · exact hε₀b p
        · exact hε₁ p
        · exact hεQ)
    refine ⟨ε₀, hε₀, fun ε hε0 hε => ?_⟩
    have hεb' : ∀ p, ‖ε‖ < ε₀b p := fun p => lt_of_lt_of_le hε (hε₀le (p, 0))
    have hε₁'' : ∀ p, ‖ε‖ < ε₁ p := fun p => lt_of_lt_of_le hε (hε₀le (p, 1))
    have hεQ' : ‖ε‖ < εQ := by
      obtain ⟨p⟩ : Nonempty (G.LimitSolutions β) := by
        rw [← not_isEmpty_iff, ← Finite.card_eq_zero_iff (α := G.LimitSolutions β)]
        rw [hcard]; exact G.Q_pos.ne'
      exact lt_of_lt_of_le hε (hε₀le (p, 2))
    -- Each branch point is an auxiliary solution.
    have hzaux : ∀ p, G.IsAuxPt (fun e => 1 + ε * c e) β (ψ p ε) := fun p =>
      hδnear p ε hε0 _ (lt_of_lt_of_le (hε₁' p ε (hε₁'' p)) (hηle.trans (hη₀δ p)))
        (hεb p ε (hεb' p)).1
    have hweak : ∀ z, G.IsAuxPt (fun e => 1 + ε * c e) β z → G.weakMap c β (ε, z) = 0 := by
      intro z hz
      have := (isAuxSolution_iff G _ β z).2 hz
      funext v; exact this.1 v
    have huniq : ∀ p z, G.IsAuxPt (fun e => 1 + ε * c e) β z →
        ‖z - G.limPt p‖ < min η₁ (sep / 2) → z = ψ p ε := fun p z hz hzp =>
      (hεb p ε (hεb' p)).2 z (lt_of_lt_of_le hzp (hη₀r p)) (hweak z hz)
    refine ⟨?_, fun p => ⟨ψ p ε, hzaux p, hε₁' p ε (hε₁'' p)⟩,
      fun p z z' hz hz' hzp hz'p => (huniq p z hz hzp).trans (huniq p z' hz' hz'p).symm⟩
    -- Surjectivity: the branch map is injective and both sides have Q elements.
    intro z hz
    let T := {q : (Dart E → ℂ) × (V → ℂ) // G.IsAuxSolution (fun e => 1 + ε * c e) β q.1 q.2}
    let φ : G.LimitSolutions β → T := fun p =>
      ⟨(fun α => ψ p ε (Sum.inl α), fun i => ψ p ε (Sum.inr i)), hzaux p⟩
    have hφ : Function.Injective φ := by
      intro p q hpq
      have hz : ψ p ε = ψ q ε := by
        funext v
        rcases v with α | i
        · exact congrFun (congrArg (fun t : T => t.1.1) hpq) α
        · exact congrFun (congrArg (fun t : T => t.1.2) hpq) i
      apply hsepP
      have h1 := hε₁' p ε (hε₁'' p)
      have h2 := hε₁' q ε (hε₁'' q)
      calc ‖G.limPt p - G.limPt q‖ = ‖(ψ q ε - G.limPt q) - (ψ p ε - G.limPt p)‖ := by
            rw [hz]; congr 1; abel
        _ ≤ ‖ψ q ε - G.limPt q‖ + ‖ψ p ε - G.limPt p‖ := norm_sub_le _ _
        _ < 2 * min η₁ (sep / 2) := by linarith
    have hTcard : Nat.card T = Nat.card (G.LimitSolutions β) := by
      rw [hcard]; exact (hQ ε hε0 hεQ').1
    have : Finite T := Nat.finite_of_card_ne_zero (by rw [hTcard, hcard]; exact G.Q_pos.ne')
    have hbij := hφ.bijective_of_nat_card_le hTcard.le
    obtain ⟨p, hp⟩ := hbij.2 ⟨(fun α => z (Sum.inl α), fun i => z (Sum.inr i)), hz⟩
    refine ⟨p, ?_⟩
    have hzp : z = ψ p ε := by
      funext v
      rcases v with α | i
      · exact (congrFun (congrArg (fun t : T => t.1.1) hp) α).symm
      · exact (congrFun (congrArg (fun t : T => t.1.2) hp) i).symm
    rw [hzp]
    exact hε₁' p ε (hε₁'' p)

theorem norm_star_sub_star (z w : Var V E → ℂ) : ‖star z - star w‖ = ‖z - w‖ := by
  rw [← star_sub, norm_star]

/-- Complexification of a real point. -/
def cplxPt (x : Var V E → ℝ) : Var V E → ℂ := fun v => (x v : ℂ)

theorem star_cplxPt (x : Var V E → ℝ) : star (cplxPt x) = cplxPt x := by
  funext v; simp [cplxPt]

theorem cplxPt_re {z : Var V E → ℂ} (hz : star z = z) :
    cplxPt (fun v => (z v).re) = z := by
  funext v
  exact Complex.conj_eq_iff_re.1 (congrFun hz v)

/-- Equivalence between real auxiliary solutions and conjugation-fixed complex auxiliary solutions. -/
def realAuxEquiv (c : E → ℝ) (β : V → ℝ) (t : ℝ) :
    {q : (Dart E → ℝ) × (V → ℝ) // G.IsAuxSolution (fun e => 1 + t * c e) β q.1 q.2} ≃
      {z : Var V E → ℂ // G.IsAuxPt (fun e => 1 + (t : ℂ) * (c e : ℂ)) (fun i => (β i : ℂ)) z ∧
        star z = z} where
  toFun q := ⟨cplxPt (Sum.elim q.1.1 q.1.2), by
    refine ⟨?_, star_cplxPt _⟩
    have := q.2.map Complex.ofRealHom
    unfold IsAuxPt
    convert this using 1 <;> funext x <;> simp [cplxPt]⟩
  invFun z := ⟨(fun α => (z.1 (Sum.inl α)).re, fun i => (z.1 (Sum.inr i)).re), by
    apply IsAuxSolution.of_map Complex.ofRealHom
    have h := z.2.1
    have hz := cplxPt_re z.2.2
    unfold IsAuxPt at h
    convert h using 1 <;> funext x <;>
      first | exact congrFun hz (Sum.inl x) | exact congrFun hz (Sum.inr x) | simp⟩
  left_inv q := by
    rcases q with ⟨⟨A, F⟩, h⟩
    simp [cplxPt]
  right_inv z := by
    apply Subtype.ext
    have hz := cplxPt_re z.2.2
    rw [← hz]
    funext v
    rcases v with α | i <;> simp [cplxPt]

/-- Equivalence between real limit solutions and conjugation-fixed complex limit solutions. -/
def realLimitEquiv (β : V → ℝ) :
    G.LimitSolutions β ≃
      {p : G.LimitSolutions (fun i => (β i : ℂ)) // star (G.limPt p) = G.limPt p} where
  toFun P := ⟨⟨(fun α => (P.1.1 α : ℂ), fun i => (P.1.2 i : ℂ)), P.2.map Complex.ofRealHom⟩, by
    funext v; rcases v with α | i <;> simp [limPt]⟩
  invFun p := ⟨(fun α => (p.1.1.1 α).re, fun i => (p.1.1.2 i).re), by
    apply IsLimitSolution.of_map Complex.ofRealHom
    have h := p.1.2
    have hz := cplxPt_re p.2
    convert h using 1 <;> funext x <;>
      first | exact congrFun hz (Sum.inl x) | exact congrFun hz (Sum.inr x) | simp⟩
  left_inv P := by
    rcases P with ⟨⟨A, F⟩, h⟩
    simp only [Complex.ofReal_re]
    rfl
  right_inv p := by
    have hz := cplxPt_re p.2
    apply Subtype.ext; apply Subtype.ext
    apply Prod.ext
    · funext α; exact congrFun hz (Sum.inl α)
    · funext i; exact congrFun hz (Sum.inr i)

/-- **Real part of main theorem A.** For real c_e≠0, β_i>0 and sufficiently small real t≠0, the number of real auxiliary solutions along s_e=1+t c_e equals the number of real limit solutions. Each is near a unique real limit point, which corresponds to an Eulerian set (`card_real_limitSolutions`). -/
theorem card_real_weak_coupling (c : E → ℝ) (hc : ∀ e, c e ≠ 0) (β : V → ℝ) (hβ : ∀ i, 0 < β i) :
    ∃ ε₀ > 0, ∀ t : ℝ, t ≠ 0 → |t| < ε₀ →
      Nat.card {q : (Dart E → ℝ) × (V → ℝ) //
        G.IsAuxSolution (fun e => 1 + t * c e) β q.1 q.2} = Nat.card (G.LimitSolutions β) := by
  classical
  set cC : E → ℂ := fun e => (c e : ℂ) with hcCdef
  set βC : V → ℂ := fun i => (β i : ℂ) with hβCdef
  have hcC : ∀ e, cC e ≠ 0 := fun e => by simpa [cC] using hc e
  have hβ0 : ∀ i, βC i ≠ 0 := fun i => by simpa [βC] using (hβ i).ne'
  have hβ1 : ∀ i, βC i ≠ -1 := fun i => by
    intro h
    have := congrArg Complex.re h
    simp [βC] at this
    linarith [hβ i]
  obtain ⟨η₀, hη₀, hsep, hmain⟩ := G.weak_coupling_master cC hcC βC hβ0 hβ1
  obtain ⟨ε₀, hε₀, hε⟩ := hmain η₀ hη₀ le_rfl
  refine ⟨ε₀, hε₀, fun t ht0 ht => ?_⟩
  have hε0 : (t : ℂ) ≠ 0 := by simpa using ht0
  have hεn : ‖(t : ℂ)‖ < ε₀ := by simpa [Complex.norm_real] using ht
  obtain ⟨hall, hex, huniq⟩ := hε (t : ℂ) hε0 hεn
  have hstarAux : ∀ z, G.IsAuxPt (fun e => 1 + (t : ℂ) * cC e) βC z →
      G.IsAuxPt (fun e => 1 + (t : ℂ) * cC e) βC (star z) := by
    intro z hz
    unfold IsAuxPt at hz ⊢
    have := hz.map (starRingEnd ℂ)
    convert this using 1 <;> funext x <;> simp [cC, βC]
  have hstarLim : ∀ p : G.LimitSolutions βC, ∃ p' : G.LimitSolutions βC,
      G.limPt p' = star (G.limPt p) := by
    intro p
    refine ⟨⟨(fun α => starRingEnd ℂ (p.1.1 α), fun i => starRingEnd ℂ (p.1.2 i)), ?_⟩, ?_⟩
    · have := p.2.map (starRingEnd ℂ)
      convert this using 1 <;> first | rfl | (funext i; simp [βC])
    · funext v; rcases v with α | i <;> rfl
  -- A conjugation-fixed auxiliary root gives a conjugation-fixed limit point.
  have hreal : ∀ z, G.IsAuxPt (fun e => 1 + (t : ℂ) * cC e) βC z → star z = z →
      ∀ p : G.LimitSolutions βC, ‖z - G.limPt p‖ < η₀ → star (G.limPt p) = G.limPt p := by
    intro z hz hzs p hp
    obtain ⟨p', hp'⟩ := hstarLim p
    have h1 : ‖z - G.limPt p'‖ < η₀ := by
      rw [hp', ← hzs, norm_star_sub_star]; exact hp
    have : p = p' := hsep p p' (by
      calc ‖G.limPt p - G.limPt p'‖ = ‖(z - G.limPt p') - (z - G.limPt p)‖ := by
            congr 1; abel
        _ ≤ ‖z - G.limPt p'‖ + ‖z - G.limPt p‖ := norm_sub_le _ _
        _ < 2 * η₀ := by linarith)
    rw [← hp', ← this]
  let Z := {z : Var V E → ℂ // G.IsAuxPt (fun e => 1 + (t : ℂ) * cC e) βC z ∧ star z = z}
  let P := {p : G.LimitSolutions βC // star (G.limPt p) = G.limPt p}
  let ζ : Z → P := fun z =>
    ⟨Classical.choose (hall z.1 z.2.1),
      hreal z.1 z.2.1 z.2.2 _ (Classical.choose_spec (hall z.1 z.2.1))⟩
  have hζ : Function.Bijective ζ := by
    constructor
    · intro z z' hzz
      have h1 := Classical.choose_spec (hall z.1 z.2.1)
      have h2 := Classical.choose_spec (hall z'.1 z'.2.1)
      have heq : Classical.choose (hall z.1 z.2.1) = Classical.choose (hall z'.1 z'.2.1) :=
        congrArg Subtype.val hzz
      rw [heq] at h1
      exact Subtype.ext (huniq _ z.1 z'.1 z.2.1 z'.2.1 h1 h2)
    · rintro ⟨p, hp⟩
      obtain ⟨z, hz, hzp⟩ := hex p
      have hzs : star z = z := by
        apply huniq p (star z) z (hstarAux z hz) hz _ hzp
        rw [← hp, norm_star_sub_star]; exact hzp
      refine ⟨⟨z, hz, hzs⟩, Subtype.ext ?_⟩
      have h1 := Classical.choose_spec (hall z hz)
      exact hsep _ _ (by
        calc ‖G.limPt (Classical.choose (hall z hz)) - G.limPt p‖ =
              ‖(z - G.limPt p) - (z - G.limPt (Classical.choose (hall z hz)))‖ := by
              congr 1; abel
          _ ≤ ‖z - G.limPt p‖ + ‖z - G.limPt (Classical.choose (hall z hz))‖ := norm_sub_le _ _
          _ < 2 * η₀ := by linarith)
  rw [Nat.card_congr (G.realAuxEquiv c β t), Nat.card_congr (G.realLimitEquiv β)]
  exact Nat.card_congr (Equiv.ofBijective ζ hζ)

/-- For connected graphs there are 2^ν real roots, as in Main Theorem A. -/
theorem card_real_weak_coupling_of_connected (hconn : G.Connected) (c : E → ℝ) (hc : ∀ e, c e ≠ 0)
    (β : V → ℝ) (hβ : ∀ i, 0 < β i) :
    ∃ ε₀ > 0, ∀ t : ℝ, t ≠ 0 → |t| < ε₀ →
      Nat.card {q : (Dart E → ℝ) × (V → ℝ) //
        G.IsAuxSolution (fun e => 1 + t * c e) β q.1 q.2} = 2 ^ G.cycleRank := by
  obtain ⟨ε₀, hε₀, h⟩ := G.card_real_weak_coupling c hc β hβ
  exact ⟨ε₀, hε₀, fun t ht0 ht => (h t ht0 ht).trans
    (G.card_real_limitSolutions_of_connected hconn β hβ)⟩

/-- **Real-root count in BP coordinates.** For loopless G, c_e≠0 and β_i>0, sufficiently small real t≠0 and any nonzero real a_e with a_e²=1+t c_e, with b_i=β_i∏_{e∋i}a_e, the number of real admissible BP solutions equals the number of real limit solutions. -/
theorem card_real_admissible_weak_coupling (hG : G.Loopless) (c : E → ℝ) (hc : ∀ e, c e ≠ 0)
    (β : V → ℝ) (hβ : ∀ i, 0 < β i) :
    ∃ ε₀ > 0, ∀ t : ℝ, t ≠ 0 → |t| < ε₀ → ∀ a : E → ℝ, (∀ e, a e ≠ 0) →
      (∀ e, a e ^ 2 = 1 + t * c e) →
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a (G.reconB a β) y} =
          Nat.card (G.LimitSolutions β) := by
  obtain ⟨ε₀, hε₀, h⟩ := G.card_real_weak_coupling c hc β hβ
  refine ⟨ε₀, hε₀, fun t ht0 ht a ha ha2 => ?_⟩
  rw [G.card_admissible_eq_card_aux hG a ha β fun i => (hβ i).ne']
  have : (fun e => a e ^ 2) = fun e => 1 + t * c e := funext ha2
  rw [this]
  exact h t ht0 ht

/-- For connected G, there are 2^ν real BP solutions along the line, giving the real-root count in main theorem A. -/
theorem card_real_admissible_weak_coupling_of_connected (hG : G.Loopless) (hconn : G.Connected)
    (c : E → ℝ) (hc : ∀ e, c e ≠ 0) (β : V → ℝ) (hβ : ∀ i, 0 < β i) :
    ∃ ε₀ > 0, ∀ t : ℝ, t ≠ 0 → |t| < ε₀ → ∀ a : E → ℝ, (∀ e, a e ≠ 0) →
      (∀ e, a e ^ 2 = 1 + t * c e) →
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a (G.reconB a β) y} = 2 ^ G.cycleRank := by
  obtain ⟨ε₀, hε₀, h⟩ := G.card_real_admissible_weak_coupling hG c hc β hβ
  exact ⟨ε₀, hε₀, fun t ht0 ht a ha ha2 => (h t ht0 ht a ha ha2).trans
    (G.card_real_limitSolutions_of_connected hconn β hβ)⟩

end Complex

end Multigraph

end BPFixedPoints

