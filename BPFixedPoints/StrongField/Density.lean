import BPFixedPoints.Degree.Generic.Count
import BPFixedPoints.Degree.WeakCoupling.Branches

/-!
# Rational parametrization of auxiliary solutions and density of generic points

Auxiliary solutions are rationally reconstructed from free coordinates (F,A₁),
A₁ e=A_{(e,true)}. For i=fst e,j=snd e,
A_{(e,false)}=(A₁e(1+F_j)+F_j−F_i)/(1+F_i),
s_e=(F_i(1+A_{(e,false)})−A₁e)/(A₁e A_{(e,false)}),
β_i=F_i^{1−d_i}∏_{α→i}A_ᾱ (`isAuxSolution_par`, `par_of_isAuxSolution`).
No square roots occur, so the generic condition g(s,β)≠0 is rational in these
coordinates. Join a solution z* to a solution z₁ with g≠0 by a complex line.
The function t↦g(s(t),β(t)) is holomorphic off finitely many denominator zeros,
a connected open set, and nonzero at t=1. The identity theorem gives nonzero
points near t=0. Thus every auxiliary solution is approximated by solutions
at generic parameters (`exists_aux_near_generic`), for `sf:degree-saturation`.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP MvPolynomial Filter Topology

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Param

variable {K : Type*} [Field K]

/-- Reconstruct A from free coordinates (F,A₁). -/
noncomputable def parA (F : V → K) (A₁ : E → K) : Dart E → K := fun α =>
  if α.2 then A₁ α.1
  else (A₁ α.1 * (1 + F (G.snd α.1)) + F (G.snd α.1) - F (G.fst α.1)) / (1 + F (G.fst α.1))

/-- s from free coordinates. -/
noncomputable def parS (F : V → K) (A₁ : E → K) (e : E) : K :=
  (F (G.fst e) * (1 + G.parA F A₁ (e, false)) - A₁ e) / (A₁ e * G.parA F A₁ (e, false))

/-- β from free coordinates. -/
noncomputable def parBeta (F : V → K) (A₁ : E → K) (i : V) : K :=
  F i ^ ((1 : ℤ) - G.degree i) * ∏ α ∈ G.inDarts i, G.parA F A₁ (rev α)

@[simp] theorem parA_true (F : V → K) (A₁ : E → K) (e : E) : G.parA F A₁ (e, true) = A₁ e := rfl

theorem parA_false (F : V → K) (A₁ : E → K) (e : E) :
    G.parA F A₁ (e, false) =
      (A₁ e * (1 + F (G.snd e)) + F (G.snd e) - F (G.fst e)) / (1 + F (G.fst e)) := rfl

/-- Free coordinates give auxiliary solutions under the nonvanishing conditions. -/
theorem isAuxSolution_par {F : V → K} {A₁ : E → K} (hA0 : ∀ α, G.parA F A₁ α ≠ 0)
    (hA1 : ∀ α, G.parA F A₁ α ≠ -1) (hF0 : ∀ i, F i ≠ 0) (hF1 : ∀ i, F i ≠ -1) :
    G.IsAuxSolution (G.parS F A₁) (G.parBeta F A₁) (G.parA F A₁) F where
  A_ne_zero := hA0
  A_ne_neg_one := hA1
  F_ne_zero := hF0
  F_ne_neg_one := hF1
  edge := by
    rintro ⟨e, _ | _⟩
    · -- α = (e, false)：tail = snd e、rev = (e, true)
      have ht := hA0 (e, true)
      have hf := hA0 (e, false)
      have h1 : 1 + F (G.fst e) ≠ 0 := fun h => hF1 _ (by linear_combination h)
      simp only [tail, Bool.cond_false, rev, Bool.not_false, parS]
      rw [parA_true] at ht ⊢
      have hdef := parA_false G F A₁ e
      rw [eq_div_iff h1] at hdef
      field_simp
      linear_combination (-1 : K) * hdef
    · -- α = (e, true)
      have ht := hA0 (e, true)
      have hf := hA0 (e, false)
      simp only [tail, Bool.cond_true, rev, Bool.not_true, parS]
      rw [parA_true] at ht ⊢
      field_simp
      ring
  vertex i := rfl

/-- Every auxiliary solution has the free-coordinate presentation. -/
theorem par_of_isAuxSolution {s : E → K} {β : V → K} {A : Dart E → K} {F : V → K}
    (h : G.IsAuxSolution s β A F) :
    G.parA F (fun e => A (e, true)) = A ∧ G.parS F (fun e => A (e, true)) = s ∧
      G.parBeta F (fun e => A (e, true)) = β := by
  have hA : G.parA F (fun e => A (e, true)) = A := by
    funext α
    rcases α with ⟨e, _ | _⟩
    · rw [parA_false]
      have h1 : 1 + F (G.fst e) ≠ 0 := fun h0 => h.F_ne_neg_one _ (by linear_combination h0)
      rw [div_eq_iff h1]
      have e1 := h.edge (e, true)
      have e2 := h.edge (e, false)
      simp only [tail, Bool.cond_true, Bool.cond_false, rev, Bool.not_true, Bool.not_false] at e1 e2
      linear_combination e2 - e1
    · rfl
  refine ⟨hA, ?_, ?_⟩
  · funext e
    unfold parS
    rw [hA]
    have e1 := h.edge (e, true)
    simp only [tail, Bool.cond_true, rev, Bool.not_true] at e1
    have h0 := h.A_ne_zero (e, true)
    have h0' := h.A_ne_zero (e, false)
    rw [div_eq_iff (mul_ne_zero h0 h0')]
    linear_combination e1
  · funext i
    unfold parBeta
    rw [hA]
    exact (h.vertex i).symm

end Param

section Density

/-- Linear polynomial c+dt. -/
noncomputable def affPoly (c d : ℂ) : Polynomial ℂ := Polynomial.C c + Polynomial.C d * Polynomial.X

theorem eval_affPoly (c d t : ℂ) : (affPoly c d).eval t = c + d * t := by
  simp [affPoly]

theorem affPoly_ne_zero {c d : ℂ} (hc : c ≠ 0) : affPoly c d ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  rw [eval_affPoly] at this
  simp at this
  exact hc this

/-- The complement of the zeros of a nonzero complex polynomial is connected, since only finitely many points are removed. -/
theorem isPreconnected_setOf_forall_eval_ne {ι : Type*} [Fintype ι] (p : ι → Polynomial ℂ)
    (hp : ∀ k, p k ≠ 0) : IsPreconnected {t : ℂ | ∀ k, (p k).eval t ≠ 0} := by
  have hc : ({t : ℂ | ∀ k, (p k).eval t ≠ 0})ᶜ.Countable := by
    have : ({t : ℂ | ∀ k, (p k).eval t ≠ 0})ᶜ = ⋃ k, {t | (p k).IsRoot t} := by
      ext t; simp [Polynomial.IsRoot]
    rw [this]
    exact Set.countable_iUnion fun k => (Polynomial.finite_setOfPred_isRoot (hp k)).countable
  have h := hc.isConnected_compl_of_one_lt_rank (E := ℂ)
    (by rw [Complex.rank_real_complex]; norm_num)
  rw [compl_compl] at h
  exact h.isPreconnected

theorem isOpen_setOf_forall_eval_ne {ι : Type*} [Fintype ι] (p : ι → Polynomial ℂ) :
    IsOpen {t : ℂ | ∀ k, (p k).eval t ≠ 0} := by
  have : {t : ℂ | ∀ k, (p k).eval t ≠ 0} = ⋂ k, {t | (p k).eval t ≠ 0} := by ext; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_ne_fun (p k).continuous continuous_const

/-- **Density of generic points.** Every neighborhood of an auxiliary solution z* contains a solution at parameters with g(s,β)≠0, provided some auxiliary solution z₁ with g≠0 exists. -/
theorem exists_aux_near_generic (g : MvPolynomial (E ⊕ V) ℤ)
    {s₁ : E → ℂ} {β₁ : V → ℂ} {A₁ : Dart E → ℂ} {F₁ : V → ℂ} (h₁ : G.IsAuxSolution s₁ β₁ A₁ F₁)
    (hg₁ : eval (Sum.elim s₁ β₁) (map (Int.castRingHom ℂ) g) ≠ 0)
    {s₀ : E → ℂ} {β₀ : V → ℂ} {A₀ : Dart E → ℂ} {F₀ : V → ℂ} (h₀ : G.IsAuxSolution s₀ β₀ A₀ F₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : E → ℂ) (β : V → ℂ) (A : Dart E → ℂ) (F : V → ℂ), G.IsAuxSolution s β A F ∧
      eval (Sum.elim s β) (map (Int.castRingHom ℂ) g) ≠ 0 ∧
      dist s s₀ < ε ∧ dist β β₀ < ε ∧ dist A A₀ < ε ∧ dist F F₀ < ε := by
  classical
  obtain ⟨hA₀, hs₀, hβ₀⟩ := G.par_of_isAuxSolution h₀
  obtain ⟨hA₁, hs₁, hβ₁⟩ := G.par_of_isAuxSolution h₁
  set a₀ : E → ℂ := fun e => A₀ (e, true)
  set a₁ : E → ℂ := fun e => A₁ (e, true)
  -- The line.
  set Fl : ℂ → V → ℂ := fun t i => F₀ i + (F₁ i - F₀ i) * t
  set al : ℂ → E → ℂ := fun t e => a₀ e + (a₁ e - a₀ e) * t
  -- Denominator polynomials.
  set pF : V → Polynomial ℂ := fun i => affPoly (F₀ i) (F₁ i - F₀ i)
  set pF1 : V → Polynomial ℂ := fun i => affPoly (1 + F₀ i) (F₁ i - F₀ i)
  set pA : E → Polynomial ℂ := fun e => affPoly (a₀ e) (a₁ e - a₀ e)
  set pN : E → Polynomial ℂ := fun e => pA e * pF1 (G.snd e) + pF (G.snd e) - pF (G.fst e)
  set P : (V ⊕ V) ⊕ (E ⊕ E) → Polynomial ℂ :=
    Sum.elim (Sum.elim pF pF1) (Sum.elim pA pN)
  have evF : ∀ i t, (pF i).eval t = Fl t i := fun i t => by simp [pF, eval_affPoly, Fl]
  have evF1 : ∀ i t, (pF1 i).eval t = 1 + Fl t i := fun i t => by
    simp [pF1, eval_affPoly, Fl]; ring
  have evA : ∀ e t, (pA e).eval t = al t e := fun e t => by simp [pA, eval_affPoly, al]
  have evN : ∀ e t, (pN e).eval t = al t e * (1 + Fl t (G.snd e)) + Fl t (G.snd e) - Fl t (G.fst e) :=
    fun e t => by simp only [pN, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      evA, evF1, evF]
  -- Nonvanishing at t=0 and t=1.
  have hN : ∀ {s : E → ℂ} {β : V → ℂ} {A : Dart E → ℂ} {F : V → ℂ}, G.IsAuxSolution s β A F → ∀ e,
      A (e, true) * (1 + F (G.snd e)) + F (G.snd e) - F (G.fst e) ≠ 0 := by
    intro s β A F h e
    obtain ⟨hA, -, -⟩ := G.par_of_isAuxSolution h
    have h1 : 1 + F (G.fst e) ≠ 0 := fun h0 => h.F_ne_neg_one _ (by linear_combination h0)
    have := congrFun hA (e, false)
    rw [parA_false, div_eq_iff h1] at this
    rw [this]
    exact mul_ne_zero (h.A_ne_zero _) h1
  have hP0 : ∀ k, (P k).eval 0 ≠ 0 := by
    rintro ((i | i) | (e | e))
    · simpa [P, evF, Fl] using h₀.F_ne_zero i
    · simp only [P, Sum.elim_inl, Sum.elim_inr, evF1, Fl, mul_zero, add_zero]
      exact fun h => h₀.F_ne_neg_one i (by linear_combination h)
    · simpa [P, evA, al] using h₀.A_ne_zero (e, true)
    · simpa [P, evN, al, Fl] using hN h₀ e
  have hP1 : ∀ k, (P k).eval 1 ≠ 0 := by
    rintro ((i | i) | (e | e))
    · simpa [P, evF, Fl] using h₁.F_ne_zero i
    · simp only [P, Sum.elim_inl, Sum.elim_inr, evF1, Fl, mul_one, add_sub_cancel]
      exact fun h => h₁.F_ne_neg_one i (by linear_combination h)
    · simpa [P, evA, al, a₁] using h₁.A_ne_zero (e, true)
    · simpa [P, evN, al, Fl, a₁] using hN h₁ e
  have hPne : ∀ k, P k ≠ 0 := fun k h => hP0 k (by rw [h]; simp)
  set U := {t : ℂ | ∀ k, (P k).eval t ≠ 0}
  have hUo : IsOpen U := isOpen_setOf_forall_eval_ne P
  have hUc : IsPreconnected U := isPreconnected_setOf_forall_eval_ne P hPne
  have h0U : (0 : ℂ) ∈ U := hP0
  have h1U : (1 : ℂ) ∈ U := hP1
  have hUF : ∀ t ∈ U, ∀ i, Fl t i ≠ 0 := fun t ht i => by
    have := ht (Sum.inl (Sum.inl i)); simpa [P, evF] using this
  have hUF1 : ∀ t ∈ U, ∀ i, 1 + Fl t i ≠ 0 := fun t ht i => by
    have := ht (Sum.inl (Sum.inr i)); simpa [P, evF1] using this
  have hUA : ∀ t ∈ U, ∀ e, al t e ≠ 0 := fun t ht e => by
    have := ht (Sum.inr (Sum.inl e)); simpa [P, evA] using this
  have hUN : ∀ t ∈ U, ∀ e,
      al t e * (1 + Fl t (G.snd e)) + Fl t (G.snd e) - Fl t (G.fst e) ≠ 0 := fun t ht e => by
    have := ht (Sum.inr (Sum.inr e)); simpa [P, evN] using this
  -- The function on the curve and its differentiability.
  set Ac : ℂ → Dart E → ℂ := fun t => G.parA (Fl t) (al t)
  set sc : ℂ → E → ℂ := fun t => G.parS (Fl t) (al t)
  set βc : ℂ → V → ℂ := fun t => G.parBeta (Fl t) (al t)
  have hdFl : ∀ i t, DifferentiableAt ℂ (fun t => Fl t i) t := fun i t => by
    simp only [Fl]; fun_prop
  have hdal : ∀ e t, DifferentiableAt ℂ (fun t => al t e) t := fun e t => by
    simp only [al]; fun_prop
  have hdA : ∀ t ∈ U, ∀ α, DifferentiableAt ℂ (fun t => Ac t α) t := by
    intro t ht α
    rcases α with ⟨e, _ | _⟩
    · simp only [Ac, parA, Bool.false_eq_true, ite_false]
      exact ((((hdal e t).mul ((differentiableAt_const _).add (hdFl _ t))).add (hdFl _ t)).sub
        (hdFl _ t)).div ((differentiableAt_const _).add (hdFl _ t)) (hUF1 t ht _)
    · simp only [Ac, parA, ite_true]; exact hdal e t
  have hAf : ∀ t ∈ U, ∀ e, Ac t (e, false) ≠ 0 := by
    intro t ht e
    simp only [Ac, parA, Bool.false_eq_true, ite_false]
    exact div_ne_zero (hUN t ht e) (hUF1 t ht _)
  have hds : ∀ t ∈ U, ∀ e, DifferentiableAt ℂ (fun t => sc t e) t := by
    intro t ht e
    simp only [sc, parS]
    exact (((hdFl _ t).mul ((differentiableAt_const _).add (hdA t ht (e, false)))).sub
      (hdal e t)).div ((hdal e t).mul (hdA t ht (e, false))) (mul_ne_zero (hUA t ht e) (hAf t ht e))
  have hdβ : ∀ t ∈ U, ∀ i, DifferentiableAt ℂ (fun t => βc t i) t := by
    intro t ht i
    simp only [βc, parBeta]
    refine ((hdFl i t).zpow (Or.inl (hUF t ht i))).mul ?_
    exact DifferentiableAt.fun_finsetProd fun α _ => hdA t ht (rev α)
  set h : ℂ → ℂ := fun t => eval (Sum.elim (sc t) (βc t)) (map (Int.castRingHom ℂ) g)
  have hdh : DifferentiableOn ℂ h U := by
    intro t ht
    have hpt : DifferentiableAt ℂ (fun t => Sum.elim (sc t) (βc t)) t := by
      rw [differentiableAt_pi]
      rintro (e | i)
      · exact hds t ht e
      · exact hdβ t ht i
    exact ((((map (Int.castRingHom ℂ) g).hasStrictFDerivAt_eval
      (Sum.elim (sc t) (βc t))).differentiableAt).comp t hpt).differentiableWithinAt
  have han : AnalyticOnNhd ℂ h U := hdh.analyticOnNhd hUo
  -- Nonvanishing at t=1.
  have hh1 : h 1 ≠ 0 := by
    have hF1 : Fl 1 = F₁ := funext fun i => by simp [Fl]
    have ha1 : al 1 = a₁ := funext fun e => by simp [al]
    simp only [h, sc, βc, hF1, ha1, hs₁, hβ₁]
    exact hg₁
  -- Nonvanishing arbitrarily near t=0.
  have hfreq : ¬ ∃ᶠ t in 𝓝[≠] (0 : ℂ), h t = 0 := by
    intro hf
    have := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc h0U hf h1U
    exact hh1 this
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), h t ≠ 0 := by
    rw [Filter.not_frequently] at hfreq; exact hfreq
  -- Value and continuity at t=0.
  have hF0 : Fl 0 = F₀ := funext fun i => by simp [Fl]
  have ha0 : al 0 = a₀ := funext fun e => by simp [al]
  have hAc0 : Ac 0 = A₀ := by simp only [Ac, hF0, ha0]; exact hA₀
  have hsc0 : sc 0 = s₀ := by simp only [sc, hF0, ha0]; exact hs₀
  have hβc0 : βc 0 = β₀ := by simp only [βc, hF0, ha0]; exact hβ₀
  have hcA : ContinuousAt Ac 0 := continuousAt_pi.2 fun α => (hdA 0 h0U α).continuousAt
  have hcs : ContinuousAt sc 0 := continuousAt_pi.2 fun e => (hds 0 h0U e).continuousAt
  have hcβ : ContinuousAt βc 0 := continuousAt_pi.2 fun i => (hdβ 0 h0U i).continuousAt
  have hcF : ContinuousAt Fl 0 := continuousAt_pi.2 fun i => (hdFl i 0).continuousAt
  have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ U ∧ dist (sc t) s₀ < ε ∧ dist (βc t) β₀ < ε ∧
      dist (Ac t) A₀ < ε ∧ dist (Fl t) F₀ < ε ∧ (∀ α, Ac t α ≠ -1) ∧ (∀ i, Fl t i ≠ -1) := by
    have hA1 : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ α, Ac t α ≠ -1 := by
      rw [Filter.eventually_all]
      intro α
      have := (continuous_apply α).continuousAt.comp hcA
      exact this.eventually (isOpen_ne.mem_nhds (by rw [Function.comp_apply, hAc0]; exact h₀.A_ne_neg_one α))
    have hF1' : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ i, Fl t i ≠ -1 := by
      rw [Filter.eventually_all]
      intro i
      have := (continuous_apply i).continuousAt.comp hcF
      exact this.eventually (isOpen_ne.mem_nhds (by rw [Function.comp_apply, hF0]; exact h₀.F_ne_neg_one i))
    filter_upwards [hUo.mem_nhds h0U,
      hcs.eventually (Metric.ball_mem_nhds _ hε) |>.mono fun t ht => by rwa [hsc0] at ht,
      hcβ.eventually (Metric.ball_mem_nhds _ hε) |>.mono fun t ht => by rwa [hβc0] at ht,
      hcA.eventually (Metric.ball_mem_nhds _ hε) |>.mono fun t ht => by rwa [hAc0] at ht,
      hcF.eventually (Metric.ball_mem_nhds _ hε) |>.mono fun t ht => by rwa [hF0] at ht,
      hA1, hF1'] with t h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨t, ⟨htU, h2, h3, h4, h5, h6, h7⟩, hht⟩ :=
    ((hnear.filter_mono nhdsWithin_le_nhds).and hev).exists
  refine ⟨sc t, βc t, Ac t, Fl t, ?_, hht, h2, h3, h4, h5⟩
  have hAc0' : ∀ α, Ac t α ≠ 0 := by
    rintro ⟨e, _ | _⟩
    · exact hAf t htU e
    · simp only [Ac, parA_true]; exact hUA t htU e
  exact G.isAuxSolution_par hAc0' h6 (hUF t htU) h7

end Density

end Multigraph

end BPFixedPoints
