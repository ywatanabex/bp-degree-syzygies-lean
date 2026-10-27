import BPFixedPoints.Real.VertexMap

/-!
# Real-root lower bound, attainment at strong fields and minimum

Using the vertex presentation in `RealSector.lean`:
`card_evenSets_le_real` gives at least #{Eulerian sets} admissible real solutions
for a_e>0, a_e≠1 and any b_i>0. Connected graphs give 2^ν
(`two_pow_cycleRank_le_real`); no finiteness is assumed, using `ENat.card`.
`sectorField_unique_strong` and `card_real_strong_field` give some H such that
all |log b_i|≥H imply exactly #{Eulerian sets} real solutions and exactly one
with all messages positive, for arbitrary signs of the log fields.
`min_real_count` and `min_real_count_of_connected` conclude
min_{b>0}R(a,b)=#H₁(G;𝔽₂), or 2^ν if connected
(`real:sector-degree`, `real:strong-field-count`, `thm:real` (ii)).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] {G : Multigraph V E}

section Count

variable {a : E → ℝ} (ha : ∀ e, 0 < a e) (ha1 : ∀ e, a e ≠ 1)
include ha ha1

/-- **All-field lower bound (`real:sector-degree`).** For every b>0, the admissible real-root count is at least the number of Eulerian edge sets. -/
theorem card_evenSets_le_real (hG : G.Loopless) {b : V → ℝ} (hb : ∀ i, 0 < b i) :
    ((Finset.univ.filter G.IsEvenSet).card : ℕ∞) ≤
      ENat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} := by
  classical
  have hsol : ∀ S : {S : Finset E // G.IsEvenSet S},
      ∃ y, G.IsAdmissibleSolution a b y ∧ negSupport y = S.1 :=
    fun S => exists_real_solution ha ha1 hG S.2 hb
  choose f hf using hsol
  let g : {S : Finset E // G.IsEvenSet S} → {y // G.IsAdmissibleSolution a b y} :=
    fun S => ⟨f S, (hf S).1⟩
  have hg : Function.Injective g := by
    intro S T h
    apply Subtype.ext
    have := congrArg (fun y => negSupport y.1) h
    simpa [g, (hf S).2, (hf T).2] using this
  have := ENat.card_le_card_of_injective hg
  rwa [ENat.card_eq_coe_fintype_card, Fintype.card_subtype] at this

/-- If connected, every b>0 has at least 2^ν admissible real solutions. -/
theorem two_pow_cycleRank_le_real (hG : G.Loopless) (hc : G.Connected) {b : V → ℝ}
    (hb : ∀ i, 0 < b i) :
    ((2 ^ G.cycleRank : ℕ) : ℕ∞) ≤ ENat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} := by
  rw [← G.card_evenSets_of_connected hc]
  exact card_evenSets_le_real ha ha1 hG hb

omit ha1 in
/-- Sector solution box bound: |(1−d_S(i))u_i−h_i|≤Σ_α|log a_α|/2. -/
theorem abs_sectorField_box {S : Finset E} {u : V → ℝ} {h : V → ℝ}
    (hu : ∀ i, G.sectorField a S u i = h i) (i : V) :
    |(1 - (G.deg S i : ℝ)) * u i - h i| ≤ ∑ α : Dart E, |Real.log (a α.1)| / 2 := by
  have h1 : (1 - (G.deg S i : ℝ)) * u i - h i = ∑ α ∈ G.inDarts i, sgnS S α * G.zP a u α := by
    have := hu i; unfold sectorField at this; linarith
  rw [h1]
  calc |∑ α ∈ G.inDarts i, sgnS S α * G.zP a u α|
      ≤ ∑ α ∈ G.inDarts i, |sgnS S α * G.zP a u α| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ α ∈ G.inDarts i, |Real.log (a α.1)| / 2 := by
        refine Finset.sum_le_sum fun α _ => ?_
        rw [abs_mul]
        have : |sgnS S α| = 1 := by unfold sgnS; split_ifs <;> simp
        rw [this, one_mul]
        exact abs_zPlus_le (ha α.1) _ _
    _ ≤ ∑ α : Dart E, |Real.log (a α.1)| / 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun α _ _ => by positivity)

omit ha1 in
/-- One-sided Lipschitz bound: when u,u' at the tail of α have the same sign and magnitude at least L+J, |z⁺_α(u)−z⁺_α(u')|≤κ(|u_t−u'_t|+|z⁺_ᾱ(u)−z⁺_ᾱ(u')|). -/
theorem abs_zP_sub_le {L J : ℝ} (hJ : ∀ e, |Real.log (a e)| / 2 ≤ J) {u u' : V → ℝ} (α : Dart E)
    (hsame : (L + J ≤ u (G.tail α) ∧ L + J ≤ u' (G.tail α)) ∨
      (u (G.tail α) ≤ -(L + J) ∧ u' (G.tail α) ≤ -(L + J))) :
    |G.zP a u α - G.zP a u' α| ≤ |a α.1 ^ 2 - 1| / a α.1 * Real.exp (-(2 * L)) *
      (|u (G.tail α) - u' (G.tail α)| + |G.zP a u (rev α) - G.zP a u' (rev α)|) := by
  have hg : ∀ w : V → ℝ, G.zP a w α = gUpd (a α.1) (w (G.tail α) - G.zP a w (rev α)) := by
    intro w
    rw [zP_rev]
    exact zPlus_eq_g (ha α.1) _ _
  have hb : ∀ w : V → ℝ, |G.zP a w (rev α)| ≤ J := fun w => by
    rw [zP_rev]; exact (abs_zPlus_le (ha α.1) _ _).trans (hJ α.1)
  rw [hg u, hg u']
  set x := u (G.tail α) - G.zP a u (rev α)
  set x' := u' (G.tail α) - G.zP a u' (rev α)
  have hxx : |x - x'| ≤ |u (G.tail α) - u' (G.tail α)| + |G.zP a u (rev α) - G.zP a u' (rev α)| := by
    have : x - x' = (u (G.tail α) - u' (G.tail α)) - (G.zP a u (rev α) - G.zP a u' (rev α)) := by
      simp only [x, x']; ring
    rw [this]; exact abs_sub _ _
  have hκ : 0 ≤ |a α.1 ^ 2 - 1| / a α.1 * Real.exp (-(2 * L)) := by
    have := ha α.1; positivity
  have hb1 := abs_le.1 (hb u)
  have hb2 := abs_le.1 (hb u')
  rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hx : L ≤ x := by simp only [x]; linarith
    have hx' : L ≤ x' := by simp only [x']; linarith
    exact (g_lipschitz_Ici (ha α.1) hx hx').trans (mul_le_mul_of_nonneg_left hxx hκ)
  · have hx : x ≤ -L := by simp only [x]; linarith
    have hx' : x' ≤ -L := by simp only [x']; linarith
    exact (g_lipschitz_Iic (ha α.1) hx hx').trans (mul_le_mul_of_nonneg_left hxx hκ)

/-- **Strong-field uniqueness, real part of `real:strong-field-count`.** For some H, all |log b_i|≥H imply at most one solution of 𝔥_S(u)=½log b in every Eulerian sector. -/
theorem sectorField_unique_strong (hG : G.Loopless) :
    ∃ H : ℝ, ∀ b : V → ℝ, (∀ i, H ≤ |Real.log (b i)|) →
      ∀ S : Finset E, G.IsEvenSet S → ∀ u u' : V → ℝ,
        (∀ i, G.sectorField a S u i = Real.log (b i) / 2) →
        (∀ i, G.sectorField a S u' i = Real.log (b i) / 2) → u = u' := by
  classical
  set c : ℝ := ∑ α : Dart E, |a α.1 ^ 2 - 1| / a α.1
  set J : ℝ := ∑ α : Dart E, |Real.log (a α.1)| / 2
  set d : ℝ := (Fintype.card (Dart E) : ℝ)
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun α _ => by have := ha α.1; positivity
  have hJ0 : 0 ≤ J := Finset.sum_nonneg fun α _ => by positivity
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hcα : ∀ α : Dart E, |a α.1 ^ 2 - 1| / a α.1 ≤ c := fun α =>
    Finset.single_le_sum (f := fun α : Dart E => |a α.1 ^ 2 - 1| / a α.1)
      (fun β _ => by have := ha β.1; positivity) (Finset.mem_univ α)
  have hJe : ∀ e, |Real.log (a e)| / 2 ≤ J := fun e =>
    Finset.single_le_sum (f := fun α : Dart E => |Real.log (a α.1)| / 2)
      (fun β _ => by positivity) (Finset.mem_univ (e, true))
  set L : ℝ := Real.log (4 * c * (d + 1) + 1) / 2
  have hL : 0 ≤ L := div_nonneg (Real.log_nonneg (by nlinarith)) zero_le_two
  set κ : ℝ := c * Real.exp (-(2 * L))
  have hexpL : Real.exp (-(2 * L)) = 1 / (4 * c * (d + 1) + 1) := by
    rw [show -(2 * L) = -Real.log (4 * c * (d + 1) + 1) by simp only [L]; ring, Real.exp_neg,
      Real.exp_log (by nlinarith), one_div]
  have hκ0 : 0 ≤ κ := mul_nonneg hc0 (Real.exp_pos _).le
  have hκ : κ * (4 * (d + 1)) ≤ 1 := by
    simp only [κ]
    rw [hexpL]
    have hpos : 0 < 4 * c * (d + 1) + 1 := by nlinarith
    rw [mul_one_div, div_mul_eq_mul_div, div_le_one hpos]
    nlinarith
  refine ⟨2 * ((L + J) * (d + 1) + J + 1), fun b hbH S hS u u' hu hu' => ?_⟩
  set h : V → ℝ := fun i => Real.log (b i) / 2
  have hbox := abs_sectorField_box ha (h := h) hu
  have hbox' := abs_sectorField_box ha (h := h) hu'
  -- Degree bound.
  have hkd : ∀ i, (G.deg S i : ℝ) ≤ d := by
    intro i
    have h1 : G.deg S i ≤ Fintype.card (Dart E) := by
      rw [← card_inDarts_filter_mem hG i]
      exact (Finset.card_filter_le _ _).trans (Finset.card_le_univ _)
    simp only [d]; exact_mod_cast h1
  have hk1 : ∀ i, (1 - (G.deg S i : ℝ)) ≠ 0 := by
    intro i hz
    have : (G.deg S i : ℝ) = 1 := by linarith
    have h1 : G.deg S i = 1 := by exact_mod_cast this
    exact Nat.not_even_one (h1 ▸ hS i)
  have hkabs : ∀ i, |1 - (G.deg S i : ℝ)| ≤ d + 1 := by
    intro i
    rw [abs_le]; constructor <;> nlinarith [hkd i, (Nat.cast_nonneg (G.deg S i) : (0 : ℝ) ≤ _)]
  have hk1' : ∀ i, 1 ≤ |1 - (G.deg S i : ℝ)| := by
    intro i
    obtain ⟨m, hm⟩ := hS i
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp [hm]
    · have : (2 : ℝ) ≤ G.deg S i := by exact_mod_cast (by omega : 2 ≤ G.deg S i)
      rw [abs_of_nonpos (by linarith)]; linarith
  -- At every vertex, u_i,u'_i have the same sign and magnitude at least L+J.
  have hlarge : ∀ i, (L + J ≤ u i ∧ L + J ≤ u' i) ∨ (u i ≤ -(L + J) ∧ u' i ≤ -(L + J)) := by
    intro i
    have hhi : (L + J) * (d + 1) + J + 1 ≤ |h i| := by
      have := hbH i
      simp only [h, abs_div, abs_two]
      linarith
    set k := 1 - (G.deg S i : ℝ)
    have hb1 := abs_le.1 (hbox i)
    have hb2 := abs_le.1 (hbox' i)
    have hk := hkabs i
    have hkpos : 0 < |k| := abs_pos.2 (hk1 i)
    -- |k u| ≥ (L+J)(d+1) + 1
    have hku : (L + J) * (d + 1) + 1 ≤ |k * u i| := by
      have := abs_sub_abs_le_abs_sub (h i) (k * u i)
      rw [abs_sub_comm] at this
      linarith [abs_le.2 hb1]
    have hku' : (L + J) * (d + 1) + 1 ≤ |k * u' i| := by
      have := abs_sub_abs_le_abs_sub (h i) (k * u' i)
      rw [abs_sub_comm] at this
      linarith [abs_le.2 hb2]
    have hui : L + J ≤ |u i| := by
      rw [abs_mul] at hku
      by_contra hlt; push Not at hlt
      have : |k| * |u i| ≤ (d + 1) * (L + J) :=
        mul_le_mul hk hlt.le (abs_nonneg _) (by linarith)
      nlinarith
    have hui' : L + J ≤ |u' i| := by
      rw [abs_mul] at hku'
      by_contra hlt; push Not at hlt
      have : |k| * |u' i| ≤ (d + 1) * (L + J) :=
        mul_le_mul hk hlt.le (abs_nonneg _) (by linarith)
      nlinarith
    -- Both ku and ku' have the sign of h.
    have hsame : 0 < (k * u i) * (k * u' i) := by
      have hJlt : J < |h i| := by nlinarith
      rcases le_or_gt 0 (h i) with hh | hh
      · rw [abs_of_nonneg hh] at hJlt
        have : 0 < k * u i := by linarith
        have : 0 < k * u' i := by linarith
        positivity
      · rw [abs_of_neg hh] at hJlt
        have h1 : k * u i < 0 := by linarith
        have h2 : k * u' i < 0 := by linarith
        exact mul_pos_of_neg_of_neg h1 h2
    have huu : 0 < u i * u' i := by
      have : (k * u i) * (k * u' i) = k ^ 2 * (u i * u' i) := by ring
      rw [this] at hsame
      exact pos_of_mul_pos_right hsame (sq_nonneg k)
    rcases le_or_gt 0 (u i) with h0 | h0
    · left
      have hu'pos : 0 < u' i := by
        rcases lt_or_eq_of_le h0 with h0' | h0'
        · exact pos_of_mul_pos_right huu h0'.le
        · rw [← h0', zero_mul] at huu; exact absurd huu (lt_irrefl 0)
      rw [abs_of_nonneg h0] at hui
      rw [abs_of_pos hu'pos] at hui'
      exact ⟨hui, hui'⟩
    · right
      have hu'neg : u' i < 0 := by
        by_contra hnn; push Not at hnn
        have : u i * u' i ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0.le hnn
        linarith
      rw [abs_of_neg h0] at hui
      rw [abs_of_neg hu'neg] at hui'
      exact ⟨by linarith, by linarith⟩
  -- Edgewise bound |Δz|≤2κm.
  set m := ‖u - u'‖
  have hm0 : 0 ≤ m := norm_nonneg _
  have hcomp : ∀ i, |u i - u' i| ≤ m := fun i => by
    have := norm_le_pi_norm (u - u') i
    simpa [Real.norm_eq_abs] using this
  have hκe : ∀ α : Dart E, |a α.1 ^ 2 - 1| / a α.1 * Real.exp (-(2 * L)) ≤ κ :=
    fun α => mul_le_mul_of_nonneg_right (hcα α) (Real.exp_pos _).le
  have hone : ∀ α : Dart E, |G.zP a u α - G.zP a u' α| ≤
      κ * (m + |G.zP a u (rev α) - G.zP a u' (rev α)|) := by
    intro α
    refine (abs_zP_sub_le ha hJe α (hlarge _)).trans ?_
    refine mul_le_mul (hκe α) ?_ (by positivity) hκ0
    linarith [hcomp (G.tail α)]
  have hdz : ∀ α : Dart E, |G.zP a u α - G.zP a u' α| ≤ 2 * κ * m := by
    intro α
    have h1 := hone α
    have h2 := hone (rev α)
    rw [rev_rev] at h2
    set δ := |G.zP a u α - G.zP a u' α|
    set δ' := |G.zP a u (rev α) - G.zP a u' (rev α)|
    have hκ4 : κ ≤ 1 / 4 := by nlinarith
    have hδ0 : 0 ≤ δ := abs_nonneg _
    have hδ'0 : 0 ≤ δ' := abs_nonneg _
    have h3 : κ * δ' ≤ κ * (κ * (m + δ)) := mul_le_mul_of_nonneg_left h2 hκ0
    nlinarith
  -- Vertexwise bound.
  have hvert : ∀ i, |u i - u' i| ≤ 2 * κ * d * m := by
    intro i
    have h1 : (1 - (G.deg S i : ℝ)) * (u i - u' i) =
        ∑ α ∈ G.inDarts i, sgnS S α * (G.zP a u α - G.zP a u' α) := by
      have e1 := hu i
      have e2 := hu' i
      unfold sectorField at e1 e2
      rw [Finset.sum_congr rfl fun α _ => mul_sub _ _ _, Finset.sum_sub_distrib]
      linarith
    calc |u i - u' i| ≤ |1 - (G.deg S i : ℝ)| * |u i - u' i| :=
          le_mul_of_one_le_left (abs_nonneg _) (hk1' i)
      _ = |∑ α ∈ G.inDarts i, sgnS S α * (G.zP a u α - G.zP a u' α)| := by rw [← abs_mul, h1]
      _ ≤ ∑ α ∈ G.inDarts i, |sgnS S α * (G.zP a u α - G.zP a u' α)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ α ∈ G.inDarts i, 2 * κ * m := by
          refine Finset.sum_le_sum fun α _ => ?_
          rw [abs_mul]
          have : |sgnS S α| = 1 := by unfold sgnS; split_ifs <;> simp
          rw [this, one_mul]
          exact hdz α
      _ = (G.inDarts i).card * (2 * κ * m) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ d * (2 * κ * m) := by
          gcongr
          simp only [d]; exact_mod_cast Finset.card_le_univ _
      _ = 2 * κ * d * m := by ring
  have hmle : m ≤ 2 * κ * d * m :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
      rw [Real.norm_eq_abs]; exact hvert i
  have hm : m = 0 := by
    have : 2 * κ * d ≤ 1 / 2 := by nlinarith
    nlinarith
  exact sub_eq_zero.1 (norm_eq_zero.1 hm)

/-- **Exact strong-field real count.** For some H, all |log b_i|≥H give exactly #{Eulerian sets} admissible real solutions and exactly one with all messages positive. -/
theorem card_real_strong_field (hG : G.Loopless) :
    ∃ H : ℝ, ∀ b : V → ℝ, (∀ i, 0 < b i) → (∀ i, H ≤ |Real.log (b i)|) →
      Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} =
          (Finset.univ.filter G.IsEvenSet).card ∧
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} = 1 := by
  classical
  obtain ⟨H, hH⟩ := sectorField_unique_strong ha ha1 hG
  refine ⟨H, fun b hb hbH => ?_⟩
  -- The negative-edge set determines the solution.
  have hinj : ∀ y y' : Dart E → ℝ, G.IsAdmissibleSolution a b y →
      G.IsAdmissibleSolution a b y' → negSupport y = negSupport y' → y = y' := by
    intro y y' hy hy' hS
    obtain ⟨e1, f1⟩ := eq_sectorMsg ha ha1 hG hb hy
    obtain ⟨e2, f2⟩ := eq_sectorMsg ha ha1 hG hb hy'
    rw [hS] at e1 f1
    have hw := hH b hbH _ (isEvenSet_negSupport hG ha hb hy') _ _ f1 f2
    calc y = _ := e1
      _ = _ := by rw [hw]
      _ = y' := e2.symm
  set Φ : {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} → {S : Finset E // G.IsEvenSet S} :=
    fun y => ⟨negSupport y.1, isEvenSet_negSupport hG ha hb y.2⟩
  have hΦ : Function.Bijective Φ := by
    refine ⟨fun y y' h => Subtype.ext (hinj y.1 y'.1 y.2 y'.2 (congrArg Subtype.val h)), ?_⟩
    intro S
    obtain ⟨y, hy, hyS⟩ := exists_real_solution ha ha1 hG S.2 hb
    exact ⟨⟨y, hy⟩, Subtype.ext hyS⟩
  refine ⟨?_, ?_⟩
  · rw [Nat.card_eq_of_bijective Φ hΦ, Nat.card_eq_fintype_card, Fintype.card_subtype]
  · have hempty : G.IsEvenSet ∅ := fun v => by simp
    obtain ⟨y₀, hy₀, hy₀S⟩ := exists_real_solution ha ha1 hG hempty hb
    have hpos₀ : ∀ α, 0 < y₀ α := by
      intro α
      have h1 : ¬ y₀ α < 0 := by
        intro h
        have := (msg_neg_iff_mem_negSupport ha hb hy₀ α).1 h
        rw [hy₀S] at this
        exact Finset.notMem_empty _ this
      exact lt_of_le_of_ne (not_lt.1 h1) (hy₀.2.1 α).symm
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨y₀, hy₀, hpos₀⟩, fun z => Subtype.ext (hinj _ _ z.2.1 hy₀ ?_)⟩
    rw [hy₀S]
    ext e
    simp only [negSupport, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_lt]
    exact (z.2.2 (e, true)).le

/-- **Minimum real-root count (`thm:real` (ii)).** For fixed a_e>0, a_e≠1, all b>0 have at least #{Eulerian sets} admissible real solutions, with equality attained at a finite fiber for some b>0. -/
theorem min_real_count (hG : G.Loopless) :
    (∀ b : V → ℝ, (∀ i, 0 < b i) → ((Finset.univ.filter G.IsEvenSet).card : ℕ∞) ≤
        ENat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y}) ∧
      ∃ b : V → ℝ, (∀ i, 0 < b i) ∧
        Finite {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} ∧
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} =
          (Finset.univ.filter G.IsEvenSet).card ∧
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} = 1 := by
  refine ⟨fun b hb => card_evenSets_le_real ha ha1 hG hb, ?_⟩
  obtain ⟨H, hH⟩ := card_real_strong_field ha ha1 hG
  refine ⟨fun _ => Real.exp (|H| + 1), fun _ => Real.exp_pos _, ?_⟩
  have hbH : ∀ i : V, H ≤ |Real.log ((fun _ => Real.exp (|H| + 1)) i)| := by
    intro i
    simp only [Real.log_exp]
    rw [abs_of_pos (by positivity)]
    linarith [le_abs_self H]
  obtain ⟨h1, h2⟩ := hH _ (fun _ => Real.exp_pos _) hbH
  refine ⟨?_, h1, h2⟩
  apply Nat.finite_of_card_ne_zero
  rw [h1]
  exact (Finset.card_pos.2 ⟨∅, by simp [IsEvenSet]⟩).ne'

/-- **Connected minimum.** min_{b>0}R(a,b)=2^ν. -/
theorem min_real_count_of_connected (hG : G.Loopless) (hc : G.Connected) :
    (∀ b : V → ℝ, (∀ i, 0 < b i) →
        ((2 ^ G.cycleRank : ℕ) : ℕ∞) ≤ ENat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y}) ∧
      ∃ b : V → ℝ, (∀ i, 0 < b i) ∧
        Finite {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} ∧
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} = 2 ^ G.cycleRank ∧
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} = 1 := by
  rw [← G.card_evenSets_of_connected hc]
  exact min_real_count ha ha1 hG

end Count

end Multigraph

end BPFixedPoints
