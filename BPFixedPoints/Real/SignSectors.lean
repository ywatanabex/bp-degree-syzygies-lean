import BPFixedPoints.Degree.Equations
import BPFixedPoints.StateSum.Parity

/-!
# Sign sectors of real BP roots (`real:sign-sectors`)

For a_e>0,b_i>0 and an admissible real solution y, all total fields are positive
(`totalField_pos`). Otherwise choose a negative F minimizing μ(F)=F/(1+F)²
=(1−m²)/4, m=(F−1)/(F+1). A negative incoming message leads to a neighboring
negative field with smaller μ, using μ_i−μ_j=a(X−Y)(XY−1)/Z² (`mu_lt`).
Opposite messages on an edge have the same sign (`neg_iff_rev_neg`).
Thus negative-message edges `negSupport y` form an Eulerian set
(`isEvenSet_negSupport`), an element of the binary cycle space.
No nonzero-coupling, simplicity or finite-fiber assumption is used; a_e=1 is allowed.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

/-- Sign of a finite product of nonzero reals: ∏f=(−1)^{number of negative factors}∏|f|. -/
theorem prod_eq_neg_one_pow_mul_prod_abs {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) :
    ∏ x ∈ s, f x = (-1) ^ (s.filter fun x => f x < 0).card * ∏ x ∈ s, |f x| := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.filter_insert, ih]
    by_cases hfa : f a < 0
    · simp only [hfa, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp [ha]), abs_of_neg hfa, pow_succ]
      ring
    · simp only [hfa, ↓reduceIte]
      rw [abs_of_nonneg (not_lt.1 hfa)]
      ring

/-- A positive finite product has an even number of negative factors. -/
theorem even_card_neg_of_prod_pos {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (h : 0 < ∏ x ∈ s, f x) : Even (s.filter fun x => f x < 0).card := by
  rw [prod_eq_neg_one_pow_mul_prod_abs] at h
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  rw [hodd.neg_one_pow, neg_one_mul] at h
  have : 0 ≤ ∏ x ∈ s, |f x| := Finset.prod_nonneg fun x _ => abs_nonneg _
  linarith

namespace BP

/-- Negative-message edge set, defined by the true orientation since both orientations have equal signs. -/
noncomputable def negSupport {E : Type*} [Fintype E] (y : Dart E → ℝ) : Finset E :=
  Finset.univ.filter fun e => y (e, true) < 0

end BP

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section RealSign

variable (a : E → ℝ) (b : V → ℝ) (y : Dart E → ℝ)

variable {G a b y}

/-- Update equation y_α(X_α+a)=aX_α+1. -/
theorem bpPoly_eq (hfix : G.IsFixedPoint a b y) (α : Dart E) :
    y α * (G.cavity b y α + a α.1) = a α.1 * G.cavity b y α + 1 := by
  have := hfix α
  unfold bpPoly at this
  linarith

/-- For a>0, a negative message has negative cavity field. -/
theorem cavity_neg_of_msg_neg (ha : ∀ e, 0 < a e) (hfix : G.IsFixedPoint a b y)
    {α : Dart E} (hα : y α < 0) : G.cavity b y α < 0 := by
  by_contra hX
  push Not at hX
  have h := bpPoly_eq hfix α
  have hpos : 0 < a α.1 * G.cavity b y α + 1 := by nlinarith [ha α.1]
  have hden : 0 < G.cavity b y α + a α.1 := by linarith [ha α.1]
  nlinarith

/-- For a>0, a positive cavity field gives a positive message. -/
theorem msg_pos_of_cavity_pos (ha : ∀ e, 0 < a e) (hfix : G.IsFixedPoint a b y)
    {α : Dart E} (hX : 0 < G.cavity b y α) : 0 < y α := by
  have h := bpPoly_eq hfix α
  have hpos : 0 < a α.1 * G.cavity b y α + 1 := by nlinarith [ha α.1]
  have hden : 0 < G.cavity b y α + a α.1 := by linarith [ha α.1]
  by_contra hy
  push Not at hy
  nlinarith

/-- Maximum-principle identity: if p(X+a)=aX+1, q(Y+a)=aY+1, F=Yp, F'=Xq, then F/(1+F)²−F'/(1+F')²=a(X−Y)(XY−1)/Z², Z=aXY+X+Y+a. -/
theorem mu_sub_mu {A X Y p q : ℝ} (hX : X + A ≠ 0) (hY : Y + A ≠ 0)
    (hp : p * (X + A) = A * X + 1) (hq : q * (Y + A) = A * Y + 1) :
    Y * p / (1 + Y * p) ^ 2 - X * q / (1 + X * q) ^ 2 =
      A * (X - Y) * (X * Y - 1) / (A * X * Y + X + Y + A) ^ 2 := by
  have hp' : p = (A * X + 1) / (X + A) := by rw [eq_div_iff hX]; exact hp
  have hq' : q = (A * Y + 1) / (Y + A) := by rw [eq_div_iff hY]; exact hq
  have h1 : 1 + Y * p = (A * X * Y + X + Y + A) / (X + A) := by
    rw [hp']; field_simp; ring
  have h2 : 1 + X * q = (A * X * Y + X + Y + A) / (Y + A) := by
    rw [hq']; field_simp; ring
  rw [h1, h2, hp', hq']
  field_simp
  ring

/-- **Total fields are positive.** At a_e>0,b_i>0, every admissible real solution has all F_i>0. -/
theorem totalField_pos (ha : ∀ e, 0 < a e) (hb : ∀ i, 0 < b i)
    (hy : G.IsAdmissibleSolution a b y) (i : V) : 0 < G.totalField b y i := by
  classical
  obtain ⟨hfix, hy0, hden, hF1⟩ := hy
  have hF0 : ∀ i, G.totalField b y i ≠ 0 :=
    G.totalField_ne_zero b y (fun i => (hb i).ne') hy0
  set F := G.totalField b y with hF
  set μ : V → ℝ := fun i => F i / (1 + F i) ^ 2
  by_contra hi
  have hineg : F i < 0 := lt_of_le_of_ne (not_lt.1 hi) (hF0 i)
  set N := Finset.univ.filter fun i => F i < 0
  have hN : N.Nonempty := ⟨i, by simp [N, hineg]⟩
  obtain ⟨k, hk, hmin⟩ := N.exists_min_image μ hN
  have hkneg : F k < 0 := (Finset.mem_filter.1 hk).2
  -- There is a negative incoming message.
  obtain ⟨α, hα, hyα⟩ : ∃ α ∈ G.inDarts k, y α < 0 := by
    by_contra hall
    push Not at hall
    have : 0 < F k := by
      rw [hF]
      unfold totalField
      exact mul_pos (hb k) (Finset.prod_pos fun α hα => lt_of_le_of_ne (hall α hα) (hy0 α).symm)
    linarith
  have hhead : G.head α = k := by simpa [inDarts] using hα
  set X := G.cavity b y α
  set Y := G.cavity b y (rev α)
  have hXneg : X < 0 := cavity_neg_of_msg_neg ha hfix hyα
  have hFk : F k = Y * y α := by
    have := G.totalField_tail_eq b y (rev α)
    rw [tail_rev, rev_rev, hhead] at this
    exact this
  have hYpos : 0 < Y := by
    by_contra hY
    push Not at hY
    have : 0 ≤ Y * y α := mul_nonneg_of_nonpos_of_nonpos hY hyα.le
    linarith
  have hqpos : 0 < y (rev α) := msg_pos_of_cavity_pos ha hfix hYpos
  set j := G.tail α
  have hFj : F j = X * y (rev α) := G.totalField_tail_eq b y α
  have hjneg : F j < 0 := by rw [hFj]; exact mul_neg_of_neg_of_pos hXneg hqpos
  have hjN : j ∈ N := by simp [N, hjneg]
  have hp := bpPoly_eq hfix α
  have hq := bpPoly_eq hfix (rev α)
  rw [rev_fst] at hq
  have hXa := hden α
  have hYa := hden (rev α)
  rw [rev_fst] at hYa
  set A := a α.1
  have hZ : A * X * Y + X + Y + A ≠ 0 := by
    have h1 : (1 + F k) * (X + A) = A * X * Y + X + Y + A := by
      rw [hFk]; linear_combination Y * hp
    rw [← h1]
    exact mul_ne_zero (hF1 k) hXa
  have hdiff := mu_sub_mu hXa hYa hp hq
  have hpos : 0 < A * (X - Y) * (X * Y - 1) / (A * X * Y + X + Y + A) ^ 2 := by
    apply div_pos _ (by positivity)
    have h1 : X - Y < 0 := by linarith
    have h2 : X * Y - 1 < 0 := by nlinarith
    exact mul_pos_of_neg_of_neg (by nlinarith [ha α.1]) h2 |>.trans_le' le_rfl
  have hlt : μ j < μ k := by
    simp only [μ]
    rw [hFk, hFj]
    linarith
  exact absurd (hmin j hjN) (not_le.2 hlt)

/-- **Opposite messages on the same edge have equal signs.** -/
theorem neg_iff_rev_neg (ha : ∀ e, 0 < a e) (hb : ∀ i, 0 < b i)
    (hy : G.IsAdmissibleSolution a b y) (α : Dart E) : y α < 0 ↔ y (rev α) < 0 := by
  have key : ∀ β : Dart E, y β < 0 → y (rev β) < 0 := by
    intro β hβ
    have hX := cavity_neg_of_msg_neg ha hy.1 hβ
    have hF := totalField_pos ha hb hy (G.tail β)
    rw [G.totalField_tail_eq b y β] at hF
    by_contra h
    push Not at h
    have : G.cavity b y β * y (rev β) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hX.le h
    linarith
  exact ⟨key α, fun h => by simpa using key (rev α) h⟩

theorem msg_neg_iff_mem_negSupport (ha : ∀ e, 0 < a e) (hb : ∀ i, 0 < b i)
    (hy : G.IsAdmissibleSolution a b y) (α : Dart E) : y α < 0 ↔ α.1 ∈ negSupport y := by
  rcases α with ⟨e, _ | _⟩
  · simp only [negSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact neg_iff_rev_neg ha hb hy (e, false)
  · simp [negSupport]

/-- **Negative edges form an Eulerian set.** For a loopless graph they have even degree at every vertex. -/
theorem isEvenSet_negSupport (hG : G.Loopless) (ha : ∀ e, 0 < a e) (hb : ∀ i, 0 < b i)
    (hy : G.IsAdmissibleSolution a b y) : G.IsEvenSet (negSupport y) := by
  classical
  intro v
  have hprod : 0 < ∏ α ∈ G.inDarts v, y α := by
    have h := totalField_pos ha hb hy v
    unfold totalField at h
    exact pos_of_mul_pos_right h (hb v).le
  have heven := even_card_neg_of_prod_pos _ _ hprod
  -- Bijection between negative incoming darts and negative edges incident to v.
  have hcard : ((G.inDarts v).filter fun α => y α < 0).card =
      G.deg (negSupport y) v := by
    have hdeg : G.deg (negSupport y) v =
        ((negSupport y).filter fun e => G.Incident e v).card := by
      unfold deg
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun e _ => ?_
      unfold endCount Incident
      have := hG e
      by_cases h1 : G.fst e = v <;> by_cases h2 : G.snd e = v
      · exact absurd (h1.trans h2.symm) this
      all_goals simp [h1, h2]
    rw [hdeg]
    apply Finset.card_bij (fun α _ => α.1)
    · intro α hα
      rw [Finset.mem_filter] at hα ⊢
      refine ⟨(msg_neg_iff_mem_negSupport ha hb hy α).1 hα.2, ?_⟩
      have := Finset.mem_filter.1 hα.1
      rcases α with ⟨e, _ | _⟩
      · exact Or.inl this.2
      · exact Or.inr this.2
    · intro α hα β hβ h
      rw [Finset.mem_filter] at hα hβ
      have h1 := (Finset.mem_filter.1 hα.1).2
      have h2 := (Finset.mem_filter.1 hβ.1).2
      rcases α with ⟨e, d⟩
      rcases β with ⟨e', d'⟩
      simp only at h
      subst h
      cases d <;> cases d'
      · rfl
      · exact absurd (h1.trans h2.symm) (hG e)
      · exact absurd (h2.trans h1.symm) (hG e)
      · rfl
    · intro e he
      rw [Finset.mem_filter] at he
      rcases he.2 with h | h
      · refine ⟨(e, false), ?_, rfl⟩
        rw [Finset.mem_filter]
        refine ⟨by simp [inDarts, head, h], ?_⟩
        exact (msg_neg_iff_mem_negSupport ha hb hy (e, false)).2 he.1
      · refine ⟨(e, true), ?_, rfl⟩
        rw [Finset.mem_filter]
        refine ⟨by simp [inDarts, head, h], ?_⟩
        exact (msg_neg_iff_mem_negSupport ha hb hy (e, true)).2 he.1
  rw [← hcard]
  exact heven

/-- **Combined statement (`real:sign-sectors`).** -/
theorem real_sign_sectors (hG : G.Loopless) (ha : ∀ e, 0 < a e) (hb : ∀ i, 0 < b i)
    (hy : G.IsAdmissibleSolution a b y) :
    (∀ i, 0 < G.totalField b y i) ∧ (∀ α, y α < 0 ↔ y (rev α) < 0) ∧
      G.IsEvenSet (negSupport y) :=
  ⟨totalField_pos ha hb hy, neg_iff_rev_neg ha hb hy, isEvenSet_negSupport hG ha hb hy⟩

end RealSign

end Multigraph

end BPFixedPoints
