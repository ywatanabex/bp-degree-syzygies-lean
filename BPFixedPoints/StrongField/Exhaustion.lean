import BPFixedPoints.StrongField.Simple

/-! # Assemble the strong-field main theorem (`thm:real` (i)) -/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

open Filter Topology

namespace Multigraph

open BP MvPolynomial

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Main

/-- Index of states and root tuples, as a product subtype. -/
def StIdx2 (a : E → ℂ) :=
  {k : Finset E × (V → ℂ) // IsState G k.1 ∧ ∀ i, k.2 i ^ G.rS k.1 i = G.C0 k.1 a i}

theorem card_stIdx2 {a : E → ℂ} (ha : ∀ e, a e ≠ 0) : Nat.card (G.StIdx2 a) = G.Q := by
  rw [← G.card_stIdx a ha]
  exact Nat.card_congr
    { toFun := fun k => ⟨⟨k.1.1, k.2.1⟩, ⟨k.1.2, k.2.2⟩⟩
      invFun := fun k => ⟨(k.1.1, k.2.1), k.1.2, k.2.2⟩
      left_inv := fun k => rfl
      right_inv := fun k => rfl }

variable {G}

theorem chartF_inj {S : Finset E} {π : V → ℂ} (hπ : ∀ i, π i ≠ 0) {z z' : Dart E ⊕ V → ℂ}
    {i : V} (h : G.chartF S π z i = G.chartF S π z' i) : z (Sum.inr i) = z' (Sum.inr i) := by
  unfold chartF at h
  split_ifs at h
  · have := inv_injective h
    exact mul_left_cancel₀ (hπ i) this
  · exact mul_left_cancel₀ (hπ i) h

/-- **All strong-field complex roots (`thm:real` (i), `sf:exhaustion`).** For loopless G and fixed a_e≠0,a_e²≠1, some ε>0 ensures exactly Q(G) simple admissible complex BP solutions whenever all p_i=b_i⁻¹ satisfy 0<‖p_i‖<ε. -/
theorem strong_field_exactly_Q_simple (hG : G.Loopless) {a : E → ℂ} (ha : ∀ e, a e ≠ 0)
    (ha1 : ∀ e, a e ^ 2 ≠ 1) :
    ∃ ε > 0, ∀ p : V → ℂ, (∀ i, p i ≠ 0) → (∀ i, ‖p i‖ < ε) →
      Nat.card {y : Dart E → ℂ // G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y} = G.Q ∧
      ∀ y, G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y →
        G.IsSimpleSolution a (fun i => (p i)⁻¹) y := by
  classical
  have hιcard : Nat.card (G.StIdx2 a) = G.Q := G.card_stIdx2 ha
  have hιfin : Finite (G.StIdx2 a) :=
    Nat.finite_of_card_ne_zero (by rw [hιcard]; exact G.Q_pos.ne')
  have hω0 : ∀ k : G.StIdx2 a, ∀ i, k.1.2 i ≠ 0 := fun k i h => by
    have := k.2.2 i
    rw [h, zero_pow (G.rS_pos _ k.2.1 i).ne'] at this
    exact C0_ne_zero ha i this.symm
  -- Branches.
  have hbr := fun k : G.StIdx2 a => exists_chart_branch k.2.1 ha k.2.2 (hω0 k)
  choose ψ hψ0 hψc hψs _ using hbr
  have hgood : ∀ k : G.StIdx2 a, ∀ᶠ x in 𝓝 (Sum.elim a 0), GoodAt G k.1.1 (ψ k) x := fun k =>
    eventually_goodAt ha ha1 (hψ0 k) (hω0 k) (hψc k) (hψs k) k.2.1
  set X : G.StIdx2 a → (V → ℂ) → (E ⊕ V → ℂ) := fun k p => Sum.elim a (G.piRoot k.1.1 p)
  have hX : ∀ k, Tendsto (X k) (𝓝 0) (𝓝 (Sum.elim a 0)) := fun k =>
    tendsto_elim_piRoot k.2.1 a
  set Y : G.StIdx2 a → (V → ℂ) → Dart E → ℂ := fun k p =>
    G.chartY k.1.1 (G.piRoot k.1.1 p) (ψ k (X k p))
  have P1 : ∀ᶠ p in 𝓝 (0 : V → ℂ), ∀ k, ∀ᶠ x in 𝓝 (X k p), GoodAt G k.1.1 (ψ k) x :=
    Filter.eventually_all.2 fun k => (hX k).eventually (hgood k).eventually_nhds
  have hYlim : ∀ k α, Tendsto (fun p => Y k p α) (𝓝 0) (𝓝 (G.limY k.1.1 a α)) := by
    intro k α
    have h1 := tendsto_chartY G (S := k.1.1) (hψ0 k) (hψc k).self_of_nhds ha α
    have h2 := h1.comp (hX k)
    refine h2.congr fun p => ?_
    rfl
  have hWlim : ∀ k i, Tendsto (fun p => ψ k (X k p) (Sum.inr i)) (𝓝 0) (𝓝 (k.1.2 i)) := by
    intro k i
    have h := (((continuous_apply (Sum.inr i)).continuousAt.comp
      (hψc k).self_of_nhds).tendsto).comp (hX k)
    have hv : (fun x => x (Sum.inr i)) ∘ ψ k = fun x => ψ k x (Sum.inr i) := rfl
    rw [Function.comp_apply, hψ0 k] at h
    exact h
  -- Distinctness.
  have P2 : ∀ᶠ p in 𝓝 (0 : V → ℂ), ∀ k k' : G.StIdx2 a, k ≠ k' →
      (k.1.1 ≠ k'.1.1 → Y k p ≠ Y k' p) ∧
        (k.1.1 = k'.1.1 → ∃ i, ψ k (X k p) (Sum.inr i) ≠ ψ k' (X k' p) (Sum.inr i)) := by
    refine Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun k' => ?_
    by_cases hkk : k = k'
    · exact Filter.Eventually.of_forall fun _ h => absurd hkk h
    · by_cases hS : k.1.1 = k'.1.1
      · have hω : k.1.2 ≠ k'.1.2 := fun h => hkk (Subtype.ext (Prod.ext hS h))
        obtain ⟨i, hi⟩ := Function.ne_iff.1 hω
        have := ((hWlim k i).sub (hWlim k' i)).eventually_ne (sub_ne_zero.2 hi)
        exact this.mono fun p hp _ => ⟨fun h => absurd hS h, fun _ => ⟨i, sub_ne_zero.1 hp⟩⟩
      · obtain ⟨e, he⟩ : ∃ e, ¬ (e ∈ k.1.1 ↔ e ∈ k'.1.1) := by
          by_contra h
          push Not at h
          exact hS (Finset.ext h)
        have hlim : G.limY k.1.1 a (e, true) ≠ G.limY k'.1.1 a (e, true) := by
          by_cases h1 : e ∈ k.1.1
          · have h2 : e ∉ k'.1.1 := fun h2 => he ⟨fun _ => h2, fun _ => h1⟩
            rw [limY_eq_zero G (S := k.1.1) (a := a) (α := (e, true)) h1]
            exact (limY_ne_zero G ha (S := k'.1.1) (α := (e, true)) h2).symm
          · have h2 : e ∈ k'.1.1 := by
              by_contra h2
              exact he ⟨fun h => absurd h h1, fun h => absurd h h2⟩
            rw [limY_eq_zero G (S := k'.1.1) (a := a) (α := (e, true)) h2]
            exact limY_ne_zero G ha (S := k.1.1) (α := (e, true)) h1
        have := ((hYlim k (e, true)).sub (hYlim k' (e, true))).eventually_ne (sub_ne_zero.2 hlim)
        exact this.mono fun p hp _ => ⟨fun _ h => hp (by rw [h, sub_self]), fun h => absurd h hS⟩
  -- Nonsingularity of the normalized matrix.
  have P3 : ∀ᶠ p in 𝓝 (0 : V → ℂ), ∀ k : G.StIdx2 a,
      (G.normC k.1.1 (X k p) (ψ k (X k p))).det ≠ 0 ∧
        ∀ α, α.1 ∈ k.1.1 → G.denS k.1.1 (X k p) (ψ k (X k p)) α ≠ 0 := by
    refine Filter.eventually_all.2 fun k => ?_
    have hcN := continuousAt_normC (S := k.1.1) ha (hψ0 k) (hψc k).self_of_nhds
    have hdet : ∀ᶠ x in 𝓝 (Sum.elim a 0), (G.normC k.1.1 x (ψ k x)).det ≠ 0 := by
      have hc := ((continuous_id.matrix_det).continuousAt).comp hcN
      have h0 : (G.normC k.1.1 (Sum.elim a 0) (ψ k (Sum.elim a 0))).det ≠ 0 := by
        rw [hψ0 k, normC_base]; exact G.det_normLim_ne_zero k.1.1 k.2.1
      exact hc.eventually_ne h0
    have hden : ∀ᶠ x in 𝓝 (Sum.elim a 0), ∀ α, α.1 ∈ k.1.1 →
        G.denS k.1.1 x (ψ k x) α ≠ 0 := by
      refine Filter.eventually_all.2 fun α => ?_
      by_cases hα : α.1 ∈ k.1.1
      · have hc : ContinuousAt (fun x => G.denS k.1.1 x (ψ k x) α) (Sum.elim a 0) := by
          have hcq : ∀ v, ContinuousAt (fun x => ψ k x v) (Sum.elim a 0) := fun v =>
            (continuous_apply v).continuousAt.comp (hψc k).self_of_nhds
          have hcx : ∀ j, ContinuousAt (fun x : E ⊕ V → ℂ => x j) (Sum.elim a 0) := fun j =>
            (continuous_apply j).continuousAt
          have hq : ψ k (Sum.elim a 0) (Sum.inl α) ≠ 0 := by
            rw [hψ0 k]; exact q0_ne_zero ha α
          unfold denS
          exact ((((hcx _).mul (hcq _)).neg.div (hcq _) hq).sub (hcx _)).mul (hcq _).neg
        have h0 : G.denS k.1.1 (Sum.elim a 0) (ψ k (Sum.elim a 0)) α ≠ 0 := by
          rw [hψ0 k]; exact denS_base ha hα
        exact (hc.eventually_ne h0).mono fun x hx _ => hx
      · exact Filter.Eventually.of_forall fun x h => absurd h hα
    exact (hX k).eventually (hdet.and hden)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 ((P1.and P2).and P3)
  refine ⟨ε, hε, fun p hp hpε => ?_⟩
  have hd : dist p 0 < ε := by rw [dist_zero_right]; exact (pi_norm_lt_iff hε).2 hpε
  obtain ⟨⟨hP1, hP2⟩, hP3⟩ := hball hd
  have hG0 : ∀ k, GoodAt G k.1.1 (ψ k) (X k p) := fun k => (hP1 k).self_of_nhds
  have hπ : ∀ k : G.StIdx2 a, ∀ i, X k p (Sum.inr i) ≠ 0 := fun k i =>
    piRoot_ne_zero k.2.1 (hp i)
  -- Admissible BP solutions.
  have hadm : ∀ k, G.IsAdmissibleSolution a (fun i => (p i)⁻¹) (Y k p) ∧
      ∀ i, G.totalField (fun i => (p i)⁻¹) (Y k p) i =
        G.chartF k.1.1 (G.piRoot k.1.1 p) (ψ k (X k p)) i := by
    intro k
    have h := (hG0 k).admissible hG k.2.1 (hπ k)
    have e1 : (fun i => X k p (Sum.inr i)) = G.piRoot k.1.1 p := rfl
    have e2 : (fun e => X k p (Sum.inl e)) = a := rfl
    rw [e1, e2, chartB_piRoot k.2.1 hp] at h
    exact h
  -- Injectivity.
  have hinj : Function.Injective fun k => Y k p := by
    intro k k' h
    by_contra hkk
    obtain ⟨h1, h2⟩ := hP2 k k' hkk
    by_cases hS : k.1.1 = k'.1.1
    · obtain ⟨i, hi⟩ := h2 hS
      apply hi
      have e1 := (hadm k).2 i
      have e2 := (hadm k').2 i
      have hY : Y k p = Y k' p := h
      rw [hY, e2] at e1
      have hπ' : ∀ j, G.piRoot k'.1.1 p j ≠ 0 := fun j => piRoot_ne_zero k'.2.1 (hp j)
      have e3 : G.chartF k'.1.1 (G.piRoot k'.1.1 p) (ψ k' (X k' p)) i =
          G.chartF k'.1.1 (G.piRoot k'.1.1 p) (ψ k (X k p)) i := by
        rw [e1]; rw [hS]
      exact (chartF_inj hπ' e3).symm
    · exact h1 hS h
  -- Preparation for the saturation lemma.
  set b0 : V → ℂ := fun i => (p i)⁻¹
  set β0 := G.auxBeta a b0
  have hb0 : ∀ i, b0 i ≠ 0 := fun i => inv_ne_zero (hp i)
  have hβ0 : ∀ i, β0 i ≠ 0 := fun i => div_ne_zero (hb0 i) (prod_inc_ne_zero ha i)
  have hrb : G.reconB a β0 = b0 := _root_.funext fun i => G.reconB_auxBeta a b0 ha i
  obtain ⟨g, hg0, hgc⟩ := G.exists_generic_aux_degree_eq_Q
  -- Auxiliary solutions at generic points.
  have hgmap : map (Int.castRingHom ℂ) g ≠ 0 := fun h =>
    hg0 (MvPolynomial.map_injective _ (RingHom.injective_int _) (h.trans (map_zero _).symm))
  obtain ⟨x1, hx1⟩ : ∃ x : E ⊕ V → ℂ, eval x (map (Int.castRingHom ℂ) g) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hgmap (MvPolynomial.funext fun x => by simpa using hall x)
  have hx1' : eval (Sum.elim (x1 ∘ Sum.inl) (x1 ∘ Sum.inr)) (map (Int.castRingHom ℂ) g) ≠ 0 := by
    rwa [Sum.elim_comp_inl_inr]
  obtain ⟨hc1, -⟩ := hgc ℂ (x1 ∘ Sum.inl) (x1 ∘ Sum.inr) hx1'
  obtain ⟨⟨⟨A1, F1⟩, hz1⟩⟩ : Nonempty {z : (Dart E → ℂ) × (V → ℂ) //
      G.IsAuxSolution (x1 ∘ Sum.inl) (x1 ∘ Sum.inr) z.1 z.2} := by
    apply (Nat.card_pos_iff.1 (by rw [hc1]; exact G.Q_pos)).1
  -- Auxiliary-coordinate branches.
  have hσ := fun k : G.StIdx2 a => auxBranch (ψ := ψ k) hG k.2.1 ha hp (hP1 k)
  have hsat := card_eq_of_saturation (P := (E → ℂ) × (V → ℂ)) (X := (Dart E → ℂ) × (V → ℂ))
    (fun q => {z | G.IsAuxSolution q.1 q.2 z.1 z.2})
    {q | eval (Sum.elim q.1 q.2) (map (Int.castRingHom ℂ) g) ≠ 0} G.Q
    (fun q hq => by
      obtain ⟨hc, -⟩ := hgc ℂ q.1 q.2 hq
      refine ⟨hc, ?_⟩
      have : Finite {z : (Dart E → ℂ) × (V → ℂ) // G.IsAuxSolution q.1 q.2 z.1 z.2} :=
        Nat.finite_of_card_ne_zero (by rw [hc]; exact G.Q_pos.ne')
      exact Set.finite_coe_iff.1 this)
    (G.qBase a p) hιcard (fun k => G.σF k.1.1 (ψ k) a p)
    (Filter.eventually_all.2 fun k => (hσ k).1) (fun k => (hσ k).2.1)
    (by
      intro k k' h
      have h' : G.σF k.1.1 (ψ k) a p (G.qBase a p) = G.σF k'.1.1 (ψ k') a p (G.qBase a p) := h
      rw [(hσ k).2.2, (hσ k').2.2] at h'
      apply hinj
      have hadm' : ∀ k, G.IsAdmissibleSolution a (G.reconB a β0) (Y k p) := fun k => by
        rw [hrb]; exact (hadm k).1
      have := (G.admissibleEquivAux hG a ha β0 hβ0).injective
        (a₁ := ⟨Y k p, hadm' k⟩) (a₂ := ⟨Y k' p, hadm' k'⟩) (by
          apply Subtype.ext
          change (G.auxA a (G.reconB a β0) (Y k p), G.totalField (G.reconB a β0) (Y k p)) =
            (G.auxA a (G.reconB a β0) (Y k' p), G.totalField (G.reconB a β0) (Y k' p))
          rw [hrb]
          exact h')
      exact congrArg Subtype.val this)
    (by
      intro z hz U hU W hW
      obtain ⟨ε₁, hε₁, hU'⟩ := Metric.mem_nhds_iff.1 hU
      obtain ⟨ε₂, hε₂, hW'⟩ := Metric.mem_nhds_iff.1 hW
      obtain ⟨s, β, A, F, hsol, hgen, hs, hβ, hA, hF⟩ :=
        G.exists_aux_near_generic g hz1 hx1' hz (lt_min hε₁ hε₂)
      refine ⟨(s, β), hU' ?_, hgen, (A, F), hW' ?_, hsol⟩
      · rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
        exact ⟨lt_of_lt_of_le hs (min_le_left _ _), lt_of_lt_of_le hβ (min_le_left _ _)⟩
      · rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
        exact ⟨lt_of_lt_of_le hA (min_le_right _ _), lt_of_lt_of_le hF (min_le_right _ _)⟩)
  have hcard := G.card_admissible_eq_card_aux hG a ha β0 hβ0
  rw [hrb] at hcard
  have hQ : Nat.card {y : Dart E → ℂ // G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y} = G.Q := by
    rw [hcard]; exact hsat
  refine ⟨hQ, ?_⟩
  -- Simplicity: every solution is some Y k p.
  have hsimp : ∀ k : G.StIdx2 a, G.IsSimpleSolution a (fun i => (p i)⁻¹) (Y k p) := by
    intro k
    have h := G.isSimple_of_det_normC hG k.2.1 (hG0 k) (hπ k) (hP3 k).2 (hP3 k).1
    have e1 : (fun i => X k p (Sum.inr i)) = G.piRoot k.1.1 p := rfl
    have e2 : (fun e => X k p (Sum.inl e)) = a := rfl
    rw [e1, e2, chartB_piRoot k.2.1 hp] at h
    exact h
  have hfinSol : Finite {y : Dart E → ℂ // G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y} :=
    Nat.finite_of_card_ne_zero (by rw [hQ]; exact G.Q_pos.ne')
  let f : G.StIdx2 a → {y : Dart E → ℂ // G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y} :=
    fun k => ⟨Y k p, (hadm k).1⟩
  have hf : Function.Bijective f := by
    refine Function.Injective.bijective_of_nat_card_le ?_ (by rw [hQ, hιcard])
    intro k k' h
    exact hinj (congrArg Subtype.val h)
  intro y hy
  obtain ⟨k, hk⟩ := hf.2 ⟨y, hy⟩
  have : y = Y k p := (congrArg Subtype.val hk).symm
  rw [this]
  exact hsimp k

/-- **Complete count of strong-field complex roots.** -/
theorem card_strong_field_eq_Q (hG : G.Loopless) {a : E → ℂ} (ha : ∀ e, a e ≠ 0)
    (ha1 : ∀ e, a e ^ 2 ≠ 1) :
    ∃ ε > 0, ∀ p : V → ℂ, (∀ i, p i ≠ 0) → (∀ i, ‖p i‖ < ε) →
      Nat.card {y : Dart E → ℂ // G.IsAdmissibleSolution a (fun i => (p i)⁻¹) y} = G.Q := by
  obtain ⟨ε, hε, h⟩ := strong_field_exactly_Q_simple hG ha ha1
  exact ⟨ε, hε, fun p hp hpε => (h p hp hpε).1⟩

end Main

end Multigraph

end BPFixedPoints
