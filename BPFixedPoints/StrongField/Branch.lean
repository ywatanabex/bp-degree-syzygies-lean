import BPFixedPoints.StrongField.Saturation

/-!
# Strong-field main theorem (`thm:real` (i), `sf:exhaustion`)

`card_strong_field_eq_Q`: for loopless G and fixed a_e≠0,a_e²≠1, there exists
ε>0 such that every b with 0<|b_i⁻¹|<ε has exactly Q(G) admissible complex BP roots.
See `StrongField/Saturation.lean` for the construction. Here assemble the open
branch conditions `GoodAt` (`eventually_goodAt`), roots π^S(p) (`piRoot`),
distinctness of indexed solutions (`eventually_injective`), and continuity
of auxiliary branches σ_k(s,β), with a(s)=a·(s/a²)^{1/2} and
π(s,β)=π⁰·(b⁰/b)^{1/r}, then apply saturation.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

open Filter Topology

namespace Multigraph

open BP MvPolynomial

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Good

variable (S : Finset E) (ψ : (E ⊕ V → ℂ) → (Dart E ⊕ V → ℂ))

/-- Conditions on branch ψ at parameter x: continuity, chart equations and open admissibility conditions. -/
structure GoodAt (x : E ⊕ V → ℂ) : Prop where
  cont : ContinuousAt ψ x
  sol : G.chartMap S (x, ψ x) = 0
  a_ne : ∀ e, x (Sum.inl e) ≠ 0
  q_ne : ∀ α, ψ x (Sum.inl α) ≠ 0
  w_ne : ∀ i, ψ x (Sum.inr i) ≠ 0
  h1 : ∀ α, 1 + x (Sum.inl α.1) * (x (Sum.inr (G.tail α)) * ψ x (Sum.inr (G.tail α))) *
    ψ x (Sum.inl (rev α)) ≠ 0
  h2 : ∀ α, x (Sum.inr (G.tail α)) * ψ x (Sum.inr (G.tail α)) +
    x (Sum.inl α.1) * ψ x (Sum.inl (rev α)) ≠ 0
  h3 : ∀ α, α.1 ∈ S → ψ x (Sum.inl (rev α)) ≠ x (Sum.inl α.1)
  h4 : ∀ i, x (Sum.inr i) * ψ x (Sum.inr i) ≠ -1

variable {G S ψ}

/-- A good branch point gives an admissible BP solution when π≠0. -/
theorem GoodAt.admissible (hG : G.Loopless) (hS : IsState G S) {x : E ⊕ V → ℂ}
    (h : GoodAt G S ψ x) (hπ : ∀ i, x (Sum.inr i) ≠ 0) :
    G.IsAdmissibleSolution (fun e => x (Sum.inl e)) (G.chartB S fun i => x (Sum.inr i))
      (G.chartY S (fun i => x (Sum.inr i)) (ψ x)) ∧
    ∀ i, G.totalField (G.chartB S fun i => x (Sum.inr i))
      (G.chartY S (fun i => x (Sum.inr i)) (ψ x)) i = G.chartF S (fun i => x (Sum.inr i)) (ψ x) i := by
  have hx : Sum.elim (fun e => x (Sum.inl e)) (fun i => x (Sum.inr i)) = x := by
    funext j; rcases j with e | i <;> rfl
  refine isAdmissibleSolution_chartBP hG hS h.a_ne hπ h.w_ne h.q_ne ?_ (fun α _ _ => h.h1 α)
    (fun α _ _ => h.h2 α) h.h3 h.h4
  rw [hx]; exact h.sol

variable {a : E → ℂ} {ω : V → ℂ}

/-- Good branch points form a neighborhood of (a,0). -/
theorem eventually_goodAt (ha : ∀ e, a e ≠ 0) (ha1 : ∀ e, a e ^ 2 ≠ 1)
    (hψ0 : ψ (Sum.elim a 0) = Sum.elim (G.q0 S a) ω) (hω0 : ∀ i, ω i ≠ 0)
    (hψc : ∀ᶠ x in 𝓝 (Sum.elim a 0), ContinuousAt ψ x)
    (hψs : ∀ᶠ x in 𝓝 (Sum.elim a 0), G.chartMap S (x, ψ x) = 0) (_hS : IsState G S) :
    ∀ᶠ x in 𝓝 (Sum.elim a 0), GoodAt G S ψ x := by
  have hc0 : ContinuousAt ψ (Sum.elim a 0) := hψc.self_of_nhds
  have hcq : ∀ v, ContinuousAt (fun x => ψ x v) (Sum.elim a 0) := fun v =>
    (continuous_apply v).continuousAt.comp hc0
  have hcx : ∀ j, ContinuousAt (fun x : E ⊕ V → ℂ => x j) (Sum.elim a 0) := fun j =>
    (continuous_apply j).continuousAt
  have hq0 : ∀ α, ψ (Sum.elim a 0) (Sum.inl α) = G.q0 S a α := fun α => by rw [hψ0]; rfl
  have hw0 : ∀ i, ψ (Sum.elim a 0) (Sum.inr i) = ω i := fun i => by rw [hψ0]; rfl
  have hne : ∀ {f : (E ⊕ V → ℂ) → ℂ} {c : ℂ}, ContinuousAt f (Sum.elim a 0) →
      f (Sum.elim a 0) ≠ c → ∀ᶠ x in 𝓝 (Sum.elim a 0), f x ≠ c := fun hf hfc =>
    hf.eventually_ne hfc
  have E1 : ∀ᶠ x in 𝓝 (Sum.elim a 0), ∀ e, x (Sum.inl e) ≠ 0 :=
    Filter.eventually_all.2 fun e => hne (hcx _) (by simpa using ha e)
  have E2 : ∀ᶠ x in 𝓝 (Sum.elim a 0), ∀ α, ψ x (Sum.inl α) ≠ 0 :=
    Filter.eventually_all.2 fun α => hne (hcq _) (by rw [hq0]; exact q0_ne_zero ha α)
  have E3 : ∀ᶠ x in 𝓝 (Sum.elim a 0), ∀ i, ψ x (Sum.inr i) ≠ 0 :=
    Filter.eventually_all.2 fun i => hne (hcq _) (by rw [hw0]; exact hω0 i)
  have E4 : ∀ᶠ x in 𝓝 (Sum.elim a 0), ∀ α, 1 + x (Sum.inl α.1) *
      (x (Sum.inr (G.tail α)) * ψ x (Sum.inr (G.tail α))) * ψ x (Sum.inl (rev α)) ≠ 0 :=
    Filter.eventually_all.2 fun α => hne
      (continuousAt_const.add (((hcx _).mul ((hcx _).mul (hcq _))).mul (hcq _)))
      (by simp)
  have E5 : ∀ᶠ x in 𝓝 (Sum.elim a 0), ∀ α, x (Sum.inr (G.tail α)) * ψ x (Sum.inr (G.tail α)) +
      x (Sum.inl α.1) * ψ x (Sum.inl (rev α)) ≠ 0 :=
    Filter.eventually_all.2 fun α => hne (((hcx _).mul (hcq _)).add ((hcx _).mul (hcq _)))
      (by simp only [Sum.elim_inr, Sum.elim_inl, Pi.zero_apply, zero_mul, zero_add, hq0]
          exact mul_ne_zero (ha _) (q0_ne_zero ha _))
  have E6 : ∀ᶠ x in 𝓝 (Sum.elim a 0), ∀ α, α.1 ∈ S →
      ψ x (Sum.inl (rev α)) ≠ x (Sum.inl α.1) := by
    refine Filter.eventually_all.2 fun α => ?_
    by_cases hα : α.1 ∈ S
    · have hhead : G.deg S (G.head α) ≠ 0 := deg_ne_zero_of_mem hα (head_incident α)
      have hlim : ψ (Sum.elim a 0) (Sum.inl (rev α)) ≠
          (Sum.elim a (0 : V → ℂ)) (Sum.inl α.1) := by
        rw [hq0]
        simp only [q0, tail_rev, rev_fst, hhead, ↓reduceIte, Sum.elim_inl]
        intro h
        apply ha1 α.1
        have := ha α.1
        field_simp at h
        linear_combination -h
      exact (((hcq _).sub (hcx _)).eventually_ne (sub_ne_zero.2 hlim)).mono
        fun x hx _ => sub_ne_zero.1 hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hα
  have E7 : ∀ᶠ x in 𝓝 (Sum.elim a 0), ∀ i, x (Sum.inr i) * ψ x (Sum.inr i) ≠ -1 :=
    Filter.eventually_all.2 fun i => hne ((hcx _).mul (hcq _)) (by simp)
  filter_upwards [hψc, hψs, E1, E2, E3, E4, E5, E6, E7] with x h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end Good

end Multigraph

end BPFixedPoints

namespace BPFixedPoints

set_option linter.unusedSectionVars false

open Filter Topology

namespace Multigraph

open BP MvPolynomial

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section RootChoice

variable (S : Finset E)

/-- Choose π^S(p) with π_i^{r_i}=(−1)^{k_i}p_i. -/
noncomputable def piRoot (p : V → ℂ) (i : V) : ℂ :=
  if h : 0 < G.rS S i then
    Classical.choose (IsAlgClosed.exists_pow_nat_eq ((-1) ^ G.deg S i * p i) h)
  else 0

variable {G S}

theorem piRoot_pow (hS : IsState G S) (p : V → ℂ) (i : V) :
    G.piRoot S p i ^ G.rS S i = (-1) ^ G.deg S i * p i := by
  unfold piRoot
  simp only [G.rS_pos S hS i, ↓reduceDIte]
  exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq _ (G.rS_pos S hS i))

theorem piRoot_ne_zero (hS : IsState G S) {p : V → ℂ} {i : V} (hp : p i ≠ 0) :
    G.piRoot S p i ≠ 0 := by
  intro h
  have := piRoot_pow hS p i
  rw [h, zero_pow (G.rS_pos S hS i).ne'] at this
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hp this.symm

theorem chartB_piRoot (hS : IsState G S) {p : V → ℂ} (hp : ∀ i, p i ≠ 0) :
    G.chartB S (G.piRoot S p) = fun i => (p i)⁻¹ := by
  funext i
  unfold chartB
  rw [piRoot_pow hS p i]
  have h1 : ((-1 : ℂ) ^ G.deg S i) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have := hp i
  field_simp

theorem tendsto_piRoot (hS : IsState G S) (i : V) :
    Tendsto (fun p : V → ℂ => G.piRoot S p i) (𝓝 0) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hr := G.rS_pos S hS i
  have hc : Tendsto (fun p : V → ℂ => p i) (𝓝 0) (𝓝 0) :=
    ((continuous_apply i).tendsto 0).congr' (by simp)
  have := (Metric.tendsto_nhds.1 hc) (ε ^ G.rS S i) (pow_pos hε _)
  filter_upwards [this] with p hp
  rw [dist_zero_right] at hp ⊢
  have hpow : ‖G.piRoot S p i‖ ^ G.rS S i = ‖p i‖ := by
    rw [← norm_pow, piRoot_pow hS, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [← hpow] at hp
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le hr.ne').1 hp

theorem tendsto_elim_piRoot (hS : IsState G S) (a : E → ℂ) :
    Tendsto (fun p : V → ℂ => Sum.elim a (G.piRoot S p)) (𝓝 0) (𝓝 (Sum.elim a 0)) := by
  rw [tendsto_pi_nhds]
  rintro (e | i)
  · exact tendsto_const_nhds
  · exact tendsto_piRoot hS i

end RootChoice

section Limits

variable {S : Finset E} {ψ : (E ⊕ V → ℂ) → (Dart E ⊕ V → ℂ)} {a : E → ℂ} {ω : V → ℂ}

/-- Message limit as p→0: zero on S and q⁰ outside S. -/
noncomputable def limY (S : Finset E) (a : E → ℂ) (α : Dart E) : ℂ :=
  if α.1 ∈ S then 0 else G.q0 S a α

/-- Messages are continuous at the base point; on S use −F_h/q with F_h=π_h w_h. -/
theorem continuousAt_chartY {x₀ : E ⊕ V → ℂ}
    (hcx : ContinuousAt ψ x₀) (hqx : ∀ α, ψ x₀ (Sum.inl α) ≠ 0) (α : Dart E) :
    ContinuousAt (fun x : E ⊕ V → ℂ => G.chartY S (fun i => x (Sum.inr i)) (ψ x) α) x₀ := by
  have hcq : ∀ v, ContinuousAt (fun x => ψ x v) x₀ := fun v =>
    (continuous_apply v).continuousAt.comp hcx
  have hcxx : ∀ j, ContinuousAt (fun x : E ⊕ V → ℂ => x j) x₀ := fun j =>
    (continuous_apply j).continuousAt
  unfold chartY chartF
  by_cases hα : α.1 ∈ S
  · simp only [hα, ↓reduceIte]
    have hh : G.deg S (G.head α) ≠ 0 := deg_ne_zero_of_mem hα (head_incident α)
    simp only [hh, ↓reduceIte]
    exact (((hcxx _).mul (hcq _)).neg).div (hcq _) (hqx α)
  · simp only [hα, ↓reduceIte]
    exact hcq _

theorem tendsto_chartY (hψ0 : ψ (Sum.elim a 0) = Sum.elim (G.q0 S a) ω)
    (hc : ContinuousAt ψ (Sum.elim a 0)) (ha : ∀ e, a e ≠ 0) (α : Dart E) :
    Tendsto (fun x : E ⊕ V → ℂ => G.chartY S (fun i => x (Sum.inr i)) (ψ x) α)
      (𝓝 (Sum.elim a 0)) (𝓝 (G.limY S a α)) := by
  have hq : ∀ α, ψ (Sum.elim a 0) (Sum.inl α) ≠ 0 := fun α => by
    rw [hψ0]; exact q0_ne_zero ha α
  have h := (continuousAt_chartY G (S := S) hc hq α).tendsto
  convert h using 2
  unfold limY chartY chartF
  by_cases hα : α.1 ∈ S
  · have hh : G.deg S (G.head α) ≠ 0 := deg_ne_zero_of_mem hα (head_incident α)
    simp [hα, hh]
  · simp only [hα, ↓reduceIte, hψ0]; rfl

theorem limY_ne_zero (ha : ∀ e, a e ≠ 0) {α : Dart E} (hα : α.1 ∉ S) : G.limY S a α ≠ 0 := by
  unfold limY; rw [ite_eq_right hα]; exact q0_ne_zero ha α

theorem limY_eq_zero {α : Dart E} (hα : α.1 ∈ S) : G.limY S a α = 0 := by
  unfold limY; rw [ite_eq_left hα]

end Limits

end Multigraph

end BPFixedPoints

namespace BPFixedPoints

set_option linter.unusedSectionVars false

open Filter Topology

namespace Multigraph

open BP MvPolynomial

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section AuxBranch

/-- a(s)=a·(s/a²)^{1/2}, using the square-root branch near s=a². -/
noncomputable def aF (a s : E → ℂ) (e : E) : ℂ := a e * (s e / a e ^ 2) ^ ((2 : ℕ) : ℂ)⁻¹

/-- b(s, β) = β ∏ a(s)。 -/
noncomputable def bF (a : E → ℂ) (q : (E → ℂ) × (V → ℂ)) : V → ℂ := G.reconB (aF a q.1) q.2

/-- π(s, β) = π⁰·(b⁰/b)^{1/r}。 -/
noncomputable def πF (S : Finset E) (a : E → ℂ) (p : V → ℂ) (q : (E → ℂ) × (V → ℂ)) (i : V) : ℂ :=
  G.piRoot S p i * ((p i)⁻¹ / G.bF a q i) ^ ((G.rS S i : ℂ)⁻¹)

noncomputable def xF (S : Finset E) (a : E → ℂ) (p : V → ℂ) (q : (E → ℂ) × (V → ℂ)) :
    E ⊕ V → ℂ :=
  Sum.elim (aF a q.1) (G.πF S a p q)

noncomputable def yF (S : Finset E) (ψ : (E ⊕ V → ℂ) → (Dart E ⊕ V → ℂ)) (a : E → ℂ) (p : V → ℂ)
    (q : (E → ℂ) × (V → ℂ)) : Dart E → ℂ :=
  G.chartY S (G.πF S a p q) (ψ (G.xF S a p q))

noncomputable def σF (S : Finset E) (ψ : (E ⊕ V → ℂ) → (Dart E ⊕ V → ℂ)) (a : E → ℂ)
    (p : V → ℂ) (q : (E → ℂ) × (V → ℂ)) : (Dart E → ℂ) × (V → ℂ) :=
  (G.auxA (aF a q.1) (G.bF a q) (G.yF S ψ a p q), G.totalField (G.bF a q) (G.yF S ψ a p q))

/-- Base point (a²,β⁰) in auxiliary coordinates. -/
noncomputable def qBase (a : E → ℂ) (p : V → ℂ) : (E → ℂ) × (V → ℂ) :=
  (fun e => a e ^ 2, G.auxBeta a fun i => (p i)⁻¹)

variable {G} {S : Finset E} {ψ : (E ⊕ V → ℂ) → (Dart E ⊕ V → ℂ)} {a : E → ℂ} {p : V → ℂ}

theorem aF_sq (ha : ∀ e, a e ≠ 0) (s : E → ℂ) (e : E) : aF a s e ^ 2 = s e := by
  unfold aF
  rw [mul_pow, Complex.cpow_nat_inv_pow _ two_ne_zero]
  have := ha e
  field_simp

theorem aF_base (ha : ∀ e, a e ≠ 0) : aF a (fun e => a e ^ 2) = a := by
  funext e
  unfold aF
  rw [div_self (pow_ne_zero _ (ha e)), Complex.one_cpow, mul_one]

theorem prod_inc_ne_zero (ha : ∀ e, a e ≠ 0) (i : V) :
    ∏ e ∈ Finset.univ.filter (fun e => G.Incident e i), a e ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun e _ => ha e

theorem bF_base (ha : ∀ e, a e ≠ 0) : G.bF a (G.qBase a p) = fun i => (p i)⁻¹ := by
  funext i
  simp only [bF, qBase, aF_base ha, reconB, auxBeta]
  rw [div_mul_cancel₀ _ (prod_inc_ne_zero ha i)]

theorem πF_base (ha : ∀ e, a e ≠ 0) (hp : ∀ i, p i ≠ 0) : G.πF S a p (G.qBase a p) = G.piRoot S p := by
  funext i
  simp only [πF, bF_base ha, div_self (inv_ne_zero (hp i)), Complex.one_cpow, mul_one]

theorem xF_base (ha : ∀ e, a e ≠ 0) (hp : ∀ i, p i ≠ 0) :
    G.xF S a p (G.qBase a p) = Sum.elim a (G.piRoot S p) := by
  unfold xF
  rw [πF_base ha hp]
  simp only [qBase, aF_base ha]

theorem continuousAt_aF (ha : ∀ e, a e ≠ 0) :
    ContinuousAt (fun q : (E → ℂ) × (V → ℂ) => aF a q.1) (G.qBase a p) := by
  refine continuousAt_pi.2 fun e => ?_
  unfold aF
  refine continuousAt_const.mul ?_
  have h1 : ContinuousAt (fun q : (E → ℂ) × (V → ℂ) => q.1 e / a e ^ 2) (G.qBase a p) :=
    ((continuous_apply e).comp continuous_fst).continuousAt.div_const _
  have h2 : (G.qBase a p).1 e / a e ^ 2 = 1 := by
    simp [qBase, div_self (pow_ne_zero _ (ha e))]
  refine ContinuousAt.comp (f := fun q : (E → ℂ) × (V → ℂ) => q.1 e / a e ^ 2)
    (g := fun z : ℂ => z ^ ((2 : ℕ) : ℂ)⁻¹) ?_ h1
  rw [h2]
  exact continuousAt_cpow_const Complex.one_mem_slitPlane

theorem continuousAt_bF (ha : ∀ e, a e ≠ 0) : ContinuousAt (G.bF a) (G.qBase a p) := by
  refine continuousAt_pi.2 fun i => ?_
  unfold bF reconB
  refine ((continuous_apply i).comp continuous_snd).continuousAt.mul ?_
  exact tendsto_finsetProd _ fun e _ =>
    (continuous_apply e).continuousAt.comp (continuousAt_aF (G := G) ha)

theorem continuousAt_πF (_hS : IsState G S) (ha : ∀ e, a e ≠ 0) (hp : ∀ i, p i ≠ 0) :
    ContinuousAt (G.πF S a p) (G.qBase a p) := by
  refine continuousAt_pi.2 fun i => ?_
  unfold πF
  refine continuousAt_const.mul ?_
  have hb : ContinuousAt (fun q => G.bF a q i) (G.qBase a p) :=
    (continuous_apply i).continuousAt.comp (continuousAt_bF ha)
  have hb0 : G.bF a (G.qBase a p) i ≠ 0 := by rw [bF_base ha]; exact inv_ne_zero (hp i)
  have h1 : ContinuousAt (fun q => (p i)⁻¹ / G.bF a q i) (G.qBase a p) :=
    continuousAt_const.div hb hb0
  have h2 : (p i)⁻¹ / G.bF a (G.qBase a p) i = 1 := by
    rw [bF_base ha]; exact div_self (inv_ne_zero (hp i))
  refine ContinuousAt.comp (f := fun q => (p i)⁻¹ / G.bF a q i)
    (g := fun z : ℂ => z ^ ((G.rS S i : ℂ)⁻¹)) ?_ h1
  rw [h2]
  exact continuousAt_cpow_const Complex.one_mem_slitPlane

theorem continuousAt_xF (hS : IsState G S) (ha : ∀ e, a e ≠ 0) (hp : ∀ i, p i ≠ 0) :
    ContinuousAt (G.xF S a p) (G.qBase a p) := by
  refine continuousAt_pi.2 ?_
  rintro (e | i)
  · exact (continuous_apply e).continuousAt.comp (continuousAt_aF (G := G) ha)
  · exact (continuous_apply i).continuousAt.comp (continuousAt_πF hS ha hp)

theorem πF_pow (hS : IsState G S) (q : (E → ℂ) × (V → ℂ)) (i : V) :
    G.πF S a p q i ^ G.rS S i = (-1) ^ G.deg S i * p i * ((p i)⁻¹ / G.bF a q i) := by
  unfold πF
  rw [mul_pow, piRoot_pow hS, Complex.cpow_nat_inv_pow _ (G.rS_pos S hS i).ne']

theorem chartB_πF (hS : IsState G S) (hp : ∀ i, p i ≠ 0) {q : (E → ℂ) × (V → ℂ)}
    (hb : ∀ i, G.bF a q i ≠ 0) : G.chartB S (G.πF S a p q) = G.bF a q := by
  funext i
  unfold chartB
  rw [πF_pow hS]
  have h1 : ((-1 : ℂ) ^ G.deg S i) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  have := hp i
  have := hb i
  field_simp

/-- **Auxiliary branches.** Near a good point, σ(s,β) solves the auxiliary system at (s,β), is continuous at the base point, and there equals the auxiliary coordinates of the admissible BP solution Y. -/
theorem auxBranch (hG : G.Loopless) (hS : IsState G S) (ha : ∀ e, a e ≠ 0) (hp : ∀ i, p i ≠ 0)
    (hgood : ∀ᶠ x in 𝓝 (Sum.elim a (G.piRoot S p)), GoodAt G S ψ x) :
    (∀ᶠ q in 𝓝 (G.qBase a p), G.IsAuxSolution q.1 q.2 (G.σF S ψ a p q).1 (G.σF S ψ a p q).2) ∧
      ContinuousAt (G.σF S ψ a p) (G.qBase a p) ∧
      G.σF S ψ a p (G.qBase a p) =
        (G.auxA a (fun i => (p i)⁻¹) (G.chartY S (G.piRoot S p) (ψ (Sum.elim a (G.piRoot S p)))),
          G.totalField (fun i => (p i)⁻¹)
            (G.chartY S (G.piRoot S p) (ψ (Sum.elim a (G.piRoot S p))))) := by
  have hxc := continuousAt_xF (G := G) hS ha hp
  have hx0 := xF_base (G := G) (S := S) ha hp
  have hg1 : ∀ᶠ q in 𝓝 (G.qBase a p), GoodAt G S ψ (G.xF S a p q) := by
    have := hxc.tendsto
    rw [hx0] at this
    exact this.eventually hgood
  have hbc := continuousAt_bF (G := G) (p := p) ha
  have hb0 : ∀ i, G.bF a (G.qBase a p) i ≠ 0 := fun i => by
    rw [bF_base ha]; exact inv_ne_zero (hp i)
  have hg2 : ∀ᶠ q in 𝓝 (G.qBase a p), ∀ i, G.bF a q i ≠ 0 :=
    Filter.eventually_all.2 fun i =>
      ((continuous_apply i).continuousAt.comp hbc).eventually_ne (hb0 i)
  have hgood0 : GoodAt G S ψ (Sum.elim a (G.piRoot S p)) := hgood.self_of_nhds
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hg1, hg2] with q hq hqb
    have haq : ∀ e, aF a q.1 e ≠ 0 := hq.a_ne
    have hπq : ∀ i, G.πF S a p q i ≠ 0 := by
      intro i h0
      have := πF_pow (G := G) (a := a) (p := p) hS q i
      rw [h0, zero_pow (G.rS_pos S hS i).ne'] at this
      have h1 : ((-1 : ℂ) ^ G.deg S i) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
      exact mul_ne_zero (mul_ne_zero h1 (hp i)) (div_ne_zero (inv_ne_zero (hp i)) (hqb i))
        this.symm
    obtain ⟨hadm, -⟩ := hq.admissible hG hS hπq
    change G.IsAdmissibleSolution (aF a q.1) (G.chartB S (G.πF S a p q)) (G.yF S ψ a p q) at hadm
    rw [chartB_πF hS hp hqb] at hadm
    have h := G.isAuxSolution_of_admissible hG (aF a q.1) (G.bF a q) (G.yF S ψ a p q) haq hqb hadm
    have e1 : (fun e => aF a q.1 e ^ 2) = q.1 := funext (aF_sq ha q.1)
    have e2 : G.auxBeta (aF a q.1) (G.bF a q) = q.2 := funext (G.auxBeta_reconB _ haq q.2)
    rw [e1, e2] at h
    exact h
  · have hyc : ∀ α, ContinuousAt (fun q => G.yF S ψ a p q α) (G.qBase a p) := by
      intro α
      have h1 := continuousAt_chartY G (S := S) (ψ := ψ) (x₀ := Sum.elim a (G.piRoot S p))
        hgood0.cont hgood0.q_ne α
      rw [← hx0] at h1
      exact h1.comp hxc
    have hyc' : ContinuousAt (G.yF S ψ a p) (G.qBase a p) := continuousAt_pi.2 hyc
    refine ContinuousAt.prodMk ?_ ?_
    · refine continuousAt_pi.2 fun α => ?_
      unfold auxA cavity
      refine ContinuousAt.div ?_ ((continuous_apply α.1).continuousAt.comp
        (continuousAt_aF (G := G) ha)) ?_
      · exact ((continuous_apply _).continuousAt.comp hbc).mul
          (tendsto_finsetProd _ fun γ _ => hyc γ)
      · simp only [qBase, aF_base ha]; exact ha _
    · refine continuousAt_pi.2 fun i => ?_
      unfold totalField
      exact ((continuous_apply i).continuousAt.comp hbc).mul
        (tendsto_finsetProd _ fun γ _ => hyc γ)
  · simp only [σF, yF]
    rw [show aF a (G.qBase a p).1 = a from aF_base ha, bF_base ha, πF_base ha hp, xF_base ha hp]

end AuxBranch

end Multigraph

end BPFixedPoints
