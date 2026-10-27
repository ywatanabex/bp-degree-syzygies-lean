import BPFixedPoints.Real.SignSectors
import BPFixedPoints.Real.EdgeBranches
import BPFixedPoints.Real.BoundedPerturbation

/-!
# Vertex maps of real sign sectors and the minimum real-root count

Fix a_e>0,a_e≠1 and b_i>0. For Eulerian S and u∈ℝ^V, F_i=e^{2u_i},
choose positive edge branches off S and negative branches on S (`sectorMsg`).
Define `sectorField` by 𝔥_{S,i}(u)=(1−d_S(i))u_i−Σ_{α→i}ε_αz⁺_α(u),
with ε=−1 on S and +1 elsewhere.

If 𝔥_S(u)=h, h_i=½log b_i, this gives an admissible solution with negative
set S (`isAdmissibleSolution_sectorMsg`, `negSupport_sectorMsg`). Conversely
every admissible real solution has this form with S its negative set and
u=½log F (`eq_sectorMsg`), proving `real:vertex-map`.
Write 𝔥_S=D_S(id−B) with B bounded C¹. `surjective_sub_of_bounded` proves
existence for every h without Brouwer degree, hence the real-root lower bound
(`card_evenSets_le_real`, `real:sector-degree`).
For all |log b_i| large, the box bound forces large u with fixed signs; the
update g in z⁺=g(u_t−z⁺_t) has a small Lipschitz constant there. Each sector
then has one solution, giving exactly #{Eulerian sets} real roots and one
positive root (`card_real_strong_field`), for arbitrary field signs without
spin gauge. Thus min_h R=#H₁, or 2^ν if connected (`min_real_count_of_connected`),
as in §5 and `thm:real` (ii).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Sector

variable (a : E → ℝ) (S : Finset E) (u : V → ℝ)

/-- Positive branch in logarithmic coordinates: half the log of the message entering the head of α. -/
noncomputable def zP (α : Dart E) : ℝ := zPlus (a α.1) (u (G.head α)) (u (G.tail α))

/-- Sign ε_α: −1 on S and +1 outside. -/
def sgnS (α : Dart E) : ℝ := if α.1 ∈ S then -1 else 1

/-- Sector-S messages: positive branches outside S, negative branches on S. -/
noncomputable def sectorMsg (α : Dart E) : ℝ :=
  if α.1 ∈ S then
    -Real.exp (2 * u (G.head α)) /
      posMsg (a α.1) (Real.exp (2 * u (G.head α))) (Real.exp (2 * u (G.tail α)))
  else posMsg (a α.1) (Real.exp (2 * u (G.head α))) (Real.exp (2 * u (G.tail α)))

/-- Vertex map 𝔥_S. -/
noncomputable def sectorField (i : V) : ℝ :=
  (1 - (G.deg S i : ℝ)) * u i - ∑ α ∈ G.inDarts i, sgnS S α * G.zP a u α

variable {G a S u}

theorem zP_rev (α : Dart E) :
    G.zP a u (rev α) = zPlus (a α.1) (u (G.tail α)) (u (G.head α)) := by
  simp [zP]

/-- For a loopless graph, the number of incoming darts at i from S is d_S(i). -/
theorem card_inDarts_filter_mem (hG : G.Loopless) (i : V) :
    ((G.inDarts i).filter fun α => α.1 ∈ S).card = G.deg S i := by
  classical
  have hdeg : G.deg S i = (S.filter fun e => G.Incident e i).card := by
    unfold deg
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    unfold endCount Incident
    have := hG e
    by_cases h1 : G.fst e = i <;> by_cases h2 : G.snd e = i
    · exact absurd (h1.trans h2.symm) this
    all_goals simp [h1, h2]
  rw [hdeg]
  apply Finset.card_bij (fun α _ => α.1)
  · intro α hα
    rw [Finset.mem_filter] at hα ⊢
    refine ⟨hα.2, ?_⟩
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
    · exact ⟨(e, false), Finset.mem_filter.2 ⟨by simp [inDarts, head, h], he.1⟩, rfl⟩
    · exact ⟨(e, true), Finset.mem_filter.2 ⟨by simp [inDarts, head, h], he.1⟩, rfl⟩

variable (ha : ∀ e, 0 < a e)
include ha

/-- Exponential expression for sector messages: y_α=ε_αe^{2w_α}. -/
theorem sectorMsg_eq_exp (α : Dart E) :
    G.sectorMsg a S u α = sgnS S α *
      Real.exp (2 * (if α.1 ∈ S then u (G.head α) - G.zP a u α else G.zP a u α)) := by
  have hz := exp_two_zPlus (ha α.1) (u (G.head α)) (u (G.tail α))
  unfold sectorMsg sgnS
  split_ifs with h
  · rw [mul_sub, Real.exp_sub]
    simp only [zP] at hz ⊢
    rw [hz]
    ring
  · simp only [zP] at hz ⊢
    rw [hz, one_mul]

theorem sectorMsg_ne_zero (α : Dart E) : G.sectorMsg a S u α ≠ 0 := by
  rw [sectorMsg_eq_exp ha]
  unfold sgnS
  split_ifs <;> simp [Real.exp_ne_zero]

/-- Vertex product: ∏_{α→i}y_α=e^{2(d_S(i)u_i+Σε_αz⁺_α)} for Eulerian S and a loopless graph. -/
theorem prod_sectorMsg (hG : G.Loopless) (hS : G.IsEvenSet S) (i : V) :
    ∏ α ∈ G.inDarts i, G.sectorMsg a S u α =
      Real.exp (2 * ((G.deg S i : ℝ) * u i + ∑ α ∈ G.inDarts i, sgnS S α * G.zP a u α)) := by
  classical
  simp_rw [sectorMsg_eq_exp ha, Finset.prod_mul_distrib, ← Real.exp_sum]
  have hsgn : ∏ α ∈ G.inDarts i, sgnS S α = 1 := by
    have : ∏ α ∈ G.inDarts i, sgnS S α =
        (-1) ^ ((G.inDarts i).filter fun α => α.1 ∈ S).card := by
      unfold sgnS
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rw [this, card_inDarts_filter_mem hG i]
    exact (hS i).neg_one_pow
  rw [hsgn, one_mul]
  congr 1
  rw [← Finset.mul_sum]
  congr 1
  have hhead : ∀ α ∈ G.inDarts i, G.head α = i := fun α hα => by simpa [inDarts] using hα
  rw [Finset.sum_congr rfl fun α hα => by rw [hhead α hα]]
  have : ∀ α : Dart E, (if α.1 ∈ S then u i - G.zP a u α else G.zP a u α) =
      (if α.1 ∈ S then u i else 0) + sgnS S α * G.zP a u α := by
    intro α; unfold sgnS; split_ifs <;> ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero,
    add_zero, nsmul_eq_mul, card_inDarts_filter_mem hG i]

/-- Total-field condition: F_i=e^{2u_i} iff 𝔥_{S,i}(u)=½log b_i. -/
theorem totalField_sectorMsg_iff (hG : G.Loopless) (hS : G.IsEvenSet S) {b : V → ℝ}
    (hb : ∀ i, 0 < b i) (i : V) :
    G.totalField b (G.sectorMsg a S u) i = Real.exp (2 * u i) ↔
      G.sectorField a S u i = Real.log (b i) / 2 := by
  unfold totalField
  rw [prod_sectorMsg ha hG hS, ← Real.exp_log (hb i), ← Real.exp_add, Real.exp_eq_exp,
    Real.exp_log (hb i)]
  unfold sectorField
  constructor <;> intro h <;> linarith

variable (ha1 : ∀ e, a e ≠ 1)
include ha1

/-- **Forward `real:vertex-map`.** If 𝔥_S(u)=h, sector messages give an admissible BP solution. -/
theorem isAdmissibleSolution_sectorMsg (hG : G.Loopless) (hS : G.IsEvenSet S) {b : V → ℝ}
    (hb : ∀ i, 0 < b i) (hu : ∀ i, G.sectorField a S u i = Real.log (b i) / 2) :
    G.IsAdmissibleSolution a b (G.sectorMsg a S u) := by
  set y := G.sectorMsg a S u
  have hF : ∀ i, G.totalField b y i = Real.exp (2 * u i) := fun i =>
    (totalField_sectorMsg_iff ha hG hS hb i).2 (hu i)
  have hy0 : ∀ α, y α ≠ 0 := sectorMsg_ne_zero ha
  -- Cavity field X_α=F_{t(α)}/y_ᾱ.
  have hcav : ∀ α, G.cavity b y α = Real.exp (2 * u (G.tail α)) / y (rev α) := by
    intro α
    have := G.totalField_tail_eq b y α
    rw [hF] at this
    rw [this, mul_div_cancel_right₀ _ (hy0 _)]
  -- Edge equations.
  have hedge : ∀ α, y α * (Real.exp (2 * u (G.tail α)) + a α.1 * y (rev α)) =
      a α.1 * Real.exp (2 * u (G.tail α)) + y (rev α) := by
    intro α
    have hFh := Real.exp_pos (2 * u (G.head α))
    have hFt := Real.exp_pos (2 * u (G.tail α))
    simp only [y, sectorMsg, rev_fst, head_rev, tail_rev]
    split_ifs with h
    · exact (negMsg_edge (ha α.1) hFh hFt).1
    · exact (posMsg_edge (ha α.1) hFh hFt).1
  -- Denominators.
  have hden : ∀ α, G.cavity b y α + a α.1 ≠ 0 := by
    intro α
    rw [hcav]
    have hFh := Real.exp_pos (2 * u (G.head α))
    have hFt := Real.exp_pos (2 * u (G.tail α))
    simp only [y, sectorMsg, rev_fst, head_rev, tail_rev]
    split_ifs with h
    · have hp := posMsg_pos (ha α.1) hFt hFh
      have hne := posMsg_ne (ha α.1) (ha1 α.1) hFt hFh
      have hsimp : Real.exp (2 * u (G.tail α)) / (-Real.exp (2 * u (G.tail α)) /
          posMsg (a α.1) (Real.exp (2 * u (G.tail α))) (Real.exp (2 * u (G.head α)))) =
          -posMsg (a α.1) (Real.exp (2 * u (G.tail α))) (Real.exp (2 * u (G.head α))) := by
        field_simp
      rw [hsimp]
      intro h0
      exact hne (by linarith)
    · have hp := posMsg_pos (ha α.1) hFt hFh
      have : 0 < Real.exp (2 * u (G.tail α)) / posMsg (a α.1) (Real.exp (2 * u (G.tail α)))
          (Real.exp (2 * u (G.head α))) + a α.1 := by
        have := ha α.1; positivity
      exact this.ne'
  refine ⟨fun α => ?_, hy0, hden, fun i => ?_⟩
  · unfold bpPoly
    rw [hcav]
    have hr := hy0 (rev α)
    have := hedge α
    field_simp
    linear_combination this
  · rw [hF]; positivity

/-- Sector messages have negative-edge set S. -/
theorem negSupport_sectorMsg : negSupport (G.sectorMsg a S u) = S := by
  ext e
  simp only [negSupport, Finset.mem_filter, Finset.mem_univ, true_and, sectorMsg]
  have hp := posMsg_pos (ha e) (Real.exp_pos (2 * u (G.head (e, true))))
    (Real.exp_pos (2 * u (G.tail (e, true))))
  split_ifs with h
  · simp only [h, iff_true]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos _)) hp
  · simp only [h, iff_false, not_lt]
    exact hp.le

/-- **Reverse `real:vertex-map`.** Every admissible real solution y is a sector message for its negative set S and u=½log F, and satisfies 𝔥_S(u)=h. -/
theorem eq_sectorMsg (hG : G.Loopless) {b : V → ℝ} (hb : ∀ i, 0 < b i) {y : Dart E → ℝ}
    (hy : G.IsAdmissibleSolution a b y) :
    y = G.sectorMsg a (negSupport y) (fun i => Real.log (G.totalField b y i) / 2) ∧
      ∀ i, G.sectorField a (negSupport y) (fun i => Real.log (G.totalField b y i) / 2) i =
        Real.log (b i) / 2 := by
  have hFpos : ∀ i, 0 < G.totalField b y i := totalField_pos ha hb hy
  have hexp : ∀ i, Real.exp (2 * (Real.log (G.totalField b y i) / 2)) = G.totalField b y i :=
    fun i => by rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log (hFpos i)]
  have hy0 : ∀ α, y α ≠ 0 := hy.2.1
  have hcav : ∀ α, G.cavity b y α = G.totalField b y (G.tail α) / y (rev α) := by
    intro α
    rw [G.totalField_tail_eq b y α, mul_div_cancel_right₀ _ (hy0 _)]
  have hE : ∀ α, y α * (G.totalField b y (G.tail α) + a α.1 * y (rev α)) =
      a α.1 * G.totalField b y (G.tail α) + y (rev α) := by
    intro α
    have h := bpPoly_eq hy.1 α
    rw [hcav] at h
    have hr := hy0 (rev α)
    field_simp at h
    linear_combination h
  have hyeq : y = G.sectorMsg a (negSupport y) (fun i => Real.log (G.totalField b y i) / 2) := by
    funext α
    have h1 := hE α
    have h2 := hE (rev α)
    rw [rev_rev, rev_fst, tail_rev] at h2
    simp only [sectorMsg, hexp]
    have hFh := hFpos (G.head α)
    have hFt := hFpos (G.tail α)
    split_ifs with hS
    · have hneg : y α < 0 := (msg_neg_iff_mem_negSupport ha hb hy α).2 hS
      exact eq_negMsg_of_neg (ha α.1) hFh hFt h1 h2 hneg
    · have hnn : ¬ y α < 0 := fun h => hS ((msg_neg_iff_mem_negSupport ha hb hy α).1 h)
      exact eq_posMsg_of_pos (ha α.1) hFh hFt h1 h2
        (lt_of_le_of_ne (not_lt.1 hnn) (hy0 α).symm)
  refine ⟨hyeq, fun i => ?_⟩
  have hS := isEvenSet_negSupport hG ha hb hy
  apply (totalField_sectorMsg_iff ha hG hS hb i).1
  rw [← hyeq, hexp]

/-- **Existence for every field (`real:sector-degree`).** For any Eulerian S and b>0, 𝔥_S(u)=h has a solution because 𝔥_S=D_S(id−B), with bounded C¹ B from |z⁺|≤|J|, and `surjective_sub_of_bounded` applies. -/
theorem exists_sectorField_eq (hS : G.IsEvenSet S) (h : V → ℝ) :
    ∃ u : V → ℝ, ∀ i, G.sectorField a S u i = h i := by
  classical
  have hk : ∀ i, (1 - (G.deg S i : ℝ)) ≠ 0 := by
    intro i hz
    have : (G.deg S i : ℝ) = 1 := by linarith
    have h1 : G.deg S i = 1 := by exact_mod_cast this
    exact (Nat.not_even_one) (h1 ▸ hS i)
  have hk1 : ∀ i, 1 ≤ |1 - (G.deg S i : ℝ)| := by
    intro i
    obtain ⟨m, hm⟩ := hS i
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp [hm]
    · have : (2 : ℝ) ≤ G.deg S i := by exact_mod_cast (by omega : 2 ≤ G.deg S i)
      rw [abs_of_nonpos (by linarith)]; linarith
  set B : (V → ℝ) → (V → ℝ) := fun u i =>
    (∑ α ∈ G.inDarts i, sgnS S α * G.zP a u α) / (1 - (G.deg S i : ℝ))
  have hzc : ∀ α : Dart E, ContDiff ℝ 1 fun u : V → ℝ => G.zP a u α := by
    intro α
    have h1 : ContDiff ℝ 1 fun u : V → ℝ => (u (G.head α), u (G.tail α)) :=
      (contDiff_apply (𝕜 := ℝ) (F' := fun _ : V => ℝ) (G.head α)).prodMk
        (contDiff_apply (𝕜 := ℝ) (F' := fun _ : V => ℝ) (G.tail α))
    have h2 : ContDiff ℝ 1 fun p : ℝ × ℝ => zPlus (a α.1) p.1 p.2 :=
      contDiff_zPlus (n := 1) (ha α.1)
    have hfun : (fun u : V → ℝ => G.zP a u α) =
        (fun p : ℝ × ℝ => zPlus (a α.1) p.1 p.2) ∘ fun u : V → ℝ => (u (G.head α), u (G.tail α)) :=
      rfl
    rw [hfun]
    exact h2.comp h1
  have hBc : ContDiff ℝ 1 B := by
    refine contDiff_pi.2 fun i => ?_
    refine ContDiff.div_const ?_ _
    exact ContDiff.sum fun α _ => contDiff_const.mul (hzc α)
  set M : ℝ := ∑ α : Dart E, |Real.log (a α.1)| / 2
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun α _ => by positivity
  have hBb : ∀ u, ‖B u‖ ≤ M := by
    intro u
    refine (pi_norm_le_iff_of_nonneg hM0).2 fun i => ?_
    rw [Real.norm_eq_abs]
    simp only [B]
    rw [abs_div]
    calc |∑ α ∈ G.inDarts i, sgnS S α * G.zP a u α| / |1 - (G.deg S i : ℝ)|
        ≤ |∑ α ∈ G.inDarts i, sgnS S α * G.zP a u α| :=
          div_le_self (abs_nonneg _) (hk1 i)
      _ ≤ ∑ α ∈ G.inDarts i, |sgnS S α * G.zP a u α| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ α ∈ G.inDarts i, |Real.log (a α.1)| / 2 := by
          refine Finset.sum_le_sum fun α _ => ?_
          rw [abs_mul]
          have : |sgnS S α| = 1 := by unfold sgnS; split_ifs <;> simp
          rw [this, one_mul]
          exact abs_zPlus_le (ha α.1) _ _
      _ ≤ M := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun α _ _ => by positivity)
  obtain ⟨u, hu⟩ := surjective_sub_of_bounded hBc hBb (fun i => h i / (1 - (G.deg S i : ℝ)))
  refine ⟨u, fun i => ?_⟩
  have hi := congrFun hu i
  simp only [B, Pi.sub_apply] at hi
  unfold sectorField
  have := hk i
  field_simp at hi
  linear_combination hi

/-- For every Eulerian S and b>0 there is an admissible real solution with negative-edge set S. -/
theorem exists_real_solution (hG : G.Loopless) (hS : G.IsEvenSet S) {b : V → ℝ}
    (hb : ∀ i, 0 < b i) :
    ∃ y, G.IsAdmissibleSolution a b y ∧ negSupport y = S := by
  obtain ⟨u, hu⟩ := exists_sectorField_eq ha ha1 hS (fun i => Real.log (b i) / 2)
  exact ⟨G.sectorMsg a S u, isAdmissibleSolution_sectorMsg ha ha1 hG hS hb hu,
    negSupport_sectorMsg ha ha1⟩

end Sector

end Multigraph

end BPFixedPoints
