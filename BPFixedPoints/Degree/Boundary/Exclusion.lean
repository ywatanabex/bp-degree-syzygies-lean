import BPFixedPoints.Degree.Boundary.SpinFlip
import BPFixedPoints.Degree.Inverse

/-!
# Boundary exclusion at weak coupling

For an admissible auxiliary solution over a valued field K with multiplicative
valuation v, assume v(s_e−1)<1, v(β_i)=1 and v(β_i+1)=1 everywhere. Then all
F_i and A_{e,i} are units and the residues of F_i avoid −1.

* §4.1: flip just the vertices with poles v(F_i)>1 to make every field integral (`SpinFlip`).
* §4.2: exclude residue F=−1. At a vertex minimizing v(1+F_i), the reduction
  of quadratic (7) is (A+1)², forcing every incident residue A=−1 and hence β̄_i=−1.
* §4.3: exclude v(F_i)<1. Each incident A is either a unit of residue −1 or a
  small root with residue A/F_i=1. Valuations force exactly one unit; leading
  coefficients again force β̄_i=−1.
* §4.4: if every F is a unit of residue different from −1, quadratic (7) has
  integral coefficients and unit leading and constant terms, so A is a unit.

This works over any valued field, not just ⋃K((t^{1/r})), and does not require looplessness.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] {G : Multigraph V E}
variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-! ### Valuation estimates from the single-edge quadratic -/

theorem val_sq_gt {a : Γ₀} (ha : 1 < a) : a < a * a := by
  have := mul_lt_mul_of_pos_left ha (lt_trans zero_lt_one ha)
  rwa [mul_one] at this

/-- If sA²+HA-F=0, v(s)=1, v(H)≤1 and v(F)≤1, then A is integral. -/
theorem val_le_one_of_quadratic {s H A F : K} (hs : v s = 1) (hH : v H ≤ 1) (hF : v F ≤ 1)
    (h : s * A ^ 2 + H * A - F = 0) : v A ≤ 1 := by
  by_contra hA
  rw [not_le] at hA
  have hsq : v (s * A ^ 2) = v A * v A := by
    rw [Valuation.map_mul, hs, one_mul, Valuation.map_pow, pow_two]
  have h1 : v (H * A) < v (s * A ^ 2) := by
    rw [hsq, Valuation.map_mul]
    calc v H * v A ≤ 1 * v A := by gcongr
      _ = v A := one_mul _
      _ < v A * v A := val_sq_gt hA
  have h2 : v (-F) < v (s * A ^ 2) := by
    rw [hsq, Valuation.map_neg]
    calc v F ≤ 1 := hF
      _ < v A := hA
      _ < v A * v A := val_sq_gt hA
  exact three_term_contra v (by linear_combination h) h1 h2

/-- If additionally v(F)=1, then A is a unit. -/
theorem val_eq_one_of_quadratic {s H A F : K} (hs : v s = 1) (hH : v H ≤ 1) (hF : v F = 1)
    (h : s * A ^ 2 + H * A - F = 0) : v A = 1 := by
  have hle := val_le_one_of_quadratic v hs hH hF.le h
  by_contra hne
  have hA : v A < 1 := lt_of_le_of_ne hle hne
  have h1 : v (H * A) < v (-F) := by
    rw [Valuation.map_neg, hF, Valuation.map_mul]
    calc v H * v A ≤ 1 * v A := by gcongr
      _ = v A := one_mul _
      _ < 1 := hA
  have h2 : v (s * A ^ 2) < v (-F) := by
    rw [Valuation.map_neg, hF, Valuation.map_mul, hs, one_mul, Valuation.map_pow]
    exact pow_lt_one_of_lt_one hA (by norm_num)
  exact three_term_contra v (by linear_combination h) h1 h2

section Graph

variable {s : E → K} {β : V → K} {A : Dart E → K} {F : V → K}

/-- Quadratic (7) for the incoming auxiliary coordinate A(rev α) at vertex i, with j=tail α. -/
theorem quadratic_at (h : G.IsAuxSolution s β A F) {i : V} {α : Dart E} (hα : α ∈ G.inDarts i) :
    s α.1 * A (rev α) ^ 2 +
      (1 - F i + (s α.1 - 1) * (1 - (1 + F i) / (1 + F (G.tail α)))) * A (rev α) - F i = 0 := by
  have hi : G.head α = i := (Finset.mem_filter.1 hα).2
  have h1 := h.edge (rev α)
  rw [tail_rev, rev_rev, rev_fst, hi] at h1
  have h2 := h.edge α
  have hJ : 1 + F (G.tail α) ≠ 0 := fun h0 => h.F_ne_neg_one _ (by linear_combination h0)
  exact BP.edge_quadratic' h1 h2 hJ

/-- Section 4.2: if all F are integral, every 1+F_i is a unit, excluding residue -1. -/
theorem val_one_add_eq_one_of_le (h : G.IsAuxSolution s β A F) (hs : ∀ e, v (s e - 1) < 1)
    (hβ : ∀ i, v (β i) = 1) (hβ1 : ∀ i, v (β i + 1) = 1) (hF : ∀ i, v (F i) ≤ 1) (i : V) :
    v (1 + F i) = 1 := by
  by_contra hcon
  have hne : (Finset.univ : Finset V).Nonempty := ⟨i, Finset.mem_univ i⟩
  obtain ⟨i₀, _, hmin⟩ := Finset.exists_min_image Finset.univ (fun j => v (1 + F j)) hne
  have hi₀ : v (1 + F i₀) < 1 := by
    have hle : v (1 + F i) ≤ 1 := by rw [add_comm]; exact val_add_one_le_one v (hF i)
    exact lt_of_le_of_lt (hmin i (Finset.mem_univ i)) (lt_of_le_of_ne hle hcon)
  have hFc : Cong v (F i₀) (-1) := (cong_neg_one_iff v).2 (by rwa [add_comm] at hi₀)
  have hFu : v (F i₀) = 1 := val_eq_one_of_cong_neg_one v hFc
  have hA : ∀ α ∈ G.inDarts i₀, Cong v (A (rev α)) (-1) := by
    intro α hα
    have hq := quadratic_at h hα
    have hsu : v (s α.1) = 1 := val_eq_one_of_sub_one_lt v (hs α.1)
    have hratio : v ((1 + F i₀) / (1 + F (G.tail α))) ≤ 1 := by
      rw [Valuation.map_div]
      exact div_le_one_of_le₀ (hmin _ (Finset.mem_univ _)) zero_le
    have hone_sub : v (1 - (1 + F i₀) / (1 + F (G.tail α))) ≤ 1 :=
      (v.map_sub _ _).trans (max_le (by simp) hratio)
    have hsmall : v ((s α.1 - 1) * (1 - (1 + F i₀) / (1 + F (G.tail α)))) < 1 :=
      val_mul_lt_one_of_lt_of_le v (hs α.1) hone_sub
    have hH : v (1 - F i₀ + (s α.1 - 1) * (1 - (1 + F i₀) / (1 + F (G.tail α)))) ≤ 1 :=
      v.map_add_le ((v.map_sub 1 (F i₀)).trans (max_le (by simp) (hF i₀))) hsmall.le
    have hX : v (A (rev α)) = 1 := val_eq_one_of_quadratic v hsu hH hFu hq
    have hbr : v ((1 - s α.1) * A (rev α) ^ 2 +
        ((1 + F i₀) - (s α.1 - 1) * (1 - (1 + F i₀) / (1 + F (G.tail α)))) * A (rev α) +
        (1 + F i₀)) < 1 := by
      refine lt_of_le_of_lt (v.map_add _ _) (max_lt (lt_of_le_of_lt (v.map_add _ _)
        (max_lt ?_ ?_)) hi₀)
      · exact val_mul_lt_one_of_lt_of_le v (by rw [Valuation.map_sub_swap]; exact hs α.1)
          (by rw [Valuation.map_pow, hX, one_pow])
      · exact val_mul_lt_one_of_lt_of_le v
          (lt_of_le_of_lt (v.map_sub _ _) (max_lt hi₀ hsmall)) hX.le
    have hsq : v ((A (rev α) + 1) ^ 2) < 1 := by
      have : (A (rev α) + 1) ^ 2 =
          (s α.1 * A (rev α) ^ 2 +
            (1 - F i₀ + (s α.1 - 1) * (1 - (1 + F i₀) / (1 + F (G.tail α)))) * A (rev α) - F i₀) +
          ((1 - s α.1) * A (rev α) ^ 2 +
            ((1 + F i₀) - (s α.1 - 1) * (1 - (1 + F i₀) / (1 + F (G.tail α)))) * A (rev α) +
            (1 + F i₀)) := by ring
      rw [this, hq, zero_add]
      exact hbr
    rw [cong_neg_one_iff]
    by_contra hge
    rw [not_lt] at hge
    rw [Valuation.map_pow] at hsq
    exact absurd hsq (not_lt.2 (one_le_pow₀ hge))
  have hd : Cong v (β i₀) (-1) := by
    rw [h.vertex i₀]
    have h1 : Cong v (F i₀ ^ ((1 : ℤ) - G.degree i₀)) ((-1 : K) ^ ((1 : ℤ) - G.degree i₀)) :=
      hFc.zpow hFu (by simp) _
    have h2 : Cong v (∏ α ∈ G.inDarts i₀, A (rev α)) (∏ _α ∈ G.inDarts i₀, (-1 : K)) :=
      Cong.prod _ _ _ (fun α hα => (val_eq_one_of_cong_neg_one v (hA α hα)).le)
        (fun _ _ => by simp) hA
    have h3 := Cong.mul (v := v) (by rw [map_zpow₀, hFu, one_zpow])
      (by rw [map_prod]; exact Finset.prod_le_one fun _ _ => by simp) h1 h2
    refine h3.trans ?_
    rw [Finset.prod_const]
    have hcard : ((-1 : K) ^ (G.inDarts i₀).card) = (-1 : K) ^ (G.degree i₀ : ℤ) := by
      rw [zpow_natCast]; rfl
    rw [hcard, ← zpow_add₀ (by norm_num : (-1 : K) ≠ 0),
      show (1 : ℤ) - G.degree i₀ + G.degree i₀ = 1 by ring, zpow_one]
    exact Cong.refl _
  exact (val_add_one_eq_one_iff v (hβ i₀).le).1 (hβ1 i₀) hd

/-- Section 4.3: if all F are integral, every F_i is a unit, excluding zero full fields. -/
theorem val_eq_one_of_le (h : G.IsAuxSolution s β A F) (hs : ∀ e, v (s e - 1) < 1)
    (hβ : ∀ i, v (β i) = 1) (hβ1 : ∀ i, v (β i + 1) = 1) (hF : ∀ i, v (F i) ≤ 1) (i : V) :
    v (F i) = 1 := by
  have hone : ∀ j, v (1 + F j) = 1 := val_one_add_eq_one_of_le v h hs hβ hβ1 hF
  by_contra hne
  have hp : v (F i) < 1 := lt_of_le_of_ne (hF i) hne
  have hp0 : v (F i) ≠ 0 := v.ne_zero_iff.2 (h.F_ne_zero i)
  have hF0 : F i ≠ 0 := h.F_ne_zero i
  -- Dichotomy for incident auxiliary coordinates.
  have hdich : ∀ α ∈ G.inDarts i,
      (v (A (rev α)) = 1 ∧ Cong v (A (rev α)) (-1)) ∨
      (v (A (rev α)) = v (F i) ∧ Cong v (A (rev α) / F i) 1) := by
    intro α hα
    have hq := quadratic_at h hα
    have hsu : v (s α.1) = 1 := val_eq_one_of_sub_one_lt v (hs α.1)
    set X := A (rev α) with hXdef
    set H := 1 - F i + (s α.1 - 1) * (1 - (1 + F i) / (1 + F (G.tail α))) with hHdef
    have hH1 : Cong v H 1 := by
      unfold Cong
      have : H - 1 = -(F i) + (s α.1 - 1) * (1 - (1 + F i) / (1 + F (G.tail α))) := by
        rw [hHdef]; ring
      rw [this]
      refine lt_of_le_of_lt (v.map_add _ _) (max_lt (by rw [Valuation.map_neg]; exact hp) ?_)
      refine val_mul_lt_one_of_lt_of_le v (hs α.1) ?_
      refine (v.map_sub _ _).trans (max_le (by simp) ?_)
      rw [Valuation.map_div, hone (G.tail α), div_one, add_comm]
      exact val_add_one_le_one v (hF i)
    have hHu : v H = 1 := val_eq_one_of_cong_one v hH1
    have hXle : v X ≤ 1 := val_le_one_of_quadratic v hsu hHu.le (hF i) hq
    have hfac : X * (s α.1 * X + H) = F i := by linear_combination hq
    rcases eq_or_lt_of_le hXle with hXu | hXlt
    · left
      refine ⟨hXu, ?_⟩
      have hsmall : v (s α.1 * X + H) < 1 := by
        have : v (X * (s α.1 * X + H)) = v (F i) := by rw [hfac]
        rw [Valuation.map_mul, hXu, one_mul] at this
        rw [this]; exact hp
      rw [cong_neg_one_iff]
      have : X + 1 = (s α.1 * X + H) - ((s α.1 - 1) * X + (H - 1)) := by ring
      rw [this]
      refine lt_of_le_of_lt (v.map_sub _ _) (max_lt hsmall ?_)
      refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ hH1)
      exact val_mul_lt_one_of_lt_of_le v (hs α.1) hXu.le
    · right
      have hsX : v (s α.1 * X) < 1 := by
        rw [mul_comm]; exact val_mul_lt_one_of_lt_of_le v hXlt hsu.le
      have hu : v (s α.1 * X + H) = 1 := val_add_eq_one_of_lt v hsX hHu
      have hvX : v X = v (F i) := by
        have : v (X * (s α.1 * X + H)) = v (F i) := by rw [hfac]
        rwa [Valuation.map_mul, hu, mul_one] at this
      refine ⟨hvX, ?_⟩
      have hne0 : s α.1 * X + H ≠ 0 := ne_zero_of_val_eq_one v hu
      have hX0 : X ≠ 0 := h.A_ne_zero _
      have hXF : X / F i = (s α.1 * X + H)⁻¹ := by
        rw [← hfac]; field_simp
      rw [hXF]
      have hc : Cong v (s α.1 * X + H) 1 := by
        unfold Cong
        have : s α.1 * X + H - 1 = s α.1 * X + (H - 1) := by ring
        rw [this]
        exact lt_of_le_of_lt (v.map_add _ _) (max_lt hsX hH1)
      have := hc.inv hu (by simp)
      rwa [inv_one] at this
  -- Number k of unit incident coordinates.
  set U := (G.inDarts i).filter (fun α => v (A (rev α)) = 1) with hUdef
  have hUc : ∀ α ∈ (G.inDarts i).filter (fun α => ¬ v (A (rev α)) = 1),
      v (A (rev α)) = v (F i) ∧ Cong v (A (rev α) / F i) 1 := by
    intro α hα
    rw [Finset.mem_filter] at hα
    rcases hdich α hα.1 with h1 | h1
    · exact absurd h1.1 hα.2
    · exact h1
  have hcard : U.card + ((G.inDarts i).filter (fun α => ¬ v (A (rev α)) = 1)).card =
      (G.inDarts i).card :=
    Finset.card_filter_add_card_filter_not (s := G.inDarts i) (fun α => v (A (rev α)) = 1)
  -- The degree satisfies d≥1; if d=0, then β=F would give v(F)=1.
  have hd : 1 ≤ G.degree i := by
    by_contra hd0
    have hd0' : G.degree i = 0 := by omega
    have hv := h.vertex i
    have hempty : G.inDarts i = ∅ := Finset.card_eq_zero.1 hd0'
    rw [hempty, Finset.prod_empty, mul_one, hd0', Nat.cast_zero, sub_zero, zpow_one] at hv
    rw [← hv] at hp
    exact lt_irrefl _ (hβ i ▸ hp)
  -- β F^{d-1} = ∏ A
  have hprod : ∏ α ∈ G.inDarts i, A (rev α) = β i * F i ^ (G.degree i - 1) := by
    have hv := h.vertex i
    rw [hv, zpow_one_sub_eq_inv hd]
    field_simp
  -- Valuation counting: v(product A)=p^{d-k}, whereas v(β F^{d-1})=p^{d-1}.
  have hval : v (F i) ^ ((G.inDarts i).filter (fun α => ¬ v (A (rev α)) = 1)).card =
      v (F i) ^ (G.degree i - 1) := by
    have h1 : v (∏ α ∈ G.inDarts i, A (rev α)) =
        v (F i) ^ ((G.inDarts i).filter (fun α => ¬ v (A (rev α)) = 1)).card := by
      rw [map_prod, ← Finset.prod_filter_mul_prod_filter_not (G.inDarts i)
        (fun α => v (A (rev α)) = 1)]
      rw [Finset.prod_eq_one (fun α hα => (Finset.mem_filter.1 hα).2), one_mul,
        Finset.prod_congr rfl (fun α hα => (hUc α hα).1), Finset.prod_const]
    rw [← h1, hprod, Valuation.map_mul, hβ i, one_mul, Valuation.map_pow]
  have hk : ((G.inDarts i).filter (fun α => ¬ v (A (rev α)) = 1)).card = G.degree i - 1 :=
    pow_right_injective_of_lt_one hp0 hp hval
  have hU1 : U.card = 1 := by
    unfold degree at hk hd
    omega
  obtain ⟨α₀, hα₀⟩ := Finset.card_eq_one.1 hU1
  have hα₀mem : α₀ ∈ U := by rw [hα₀]; exact Finset.mem_singleton_self α₀
  rw [hUdef, Finset.mem_filter] at hα₀mem
  obtain ⟨hα₀in, hα₀u⟩ := hα₀mem
  have hα₀c : Cong v (A (rev α₀)) (-1) := by
    rcases hdich α₀ hα₀in with h1 | h1
    · exact h1.2
    · exact absurd (h1.1.symm ▸ hp) (by rw [hα₀u]; exact lt_irrefl _)
  -- Write β=A(rev α₀) times the product of A/F over the small roots.
  have hsplit : ∏ α ∈ G.inDarts i, A (rev α) =
      A (rev α₀) * (F i ^ (G.degree i - 1) *
        ∏ α ∈ (G.inDarts i).filter (fun α => ¬ v (A (rev α)) = 1), A (rev α) / F i) := by
    rw [← Finset.prod_filter_mul_prod_filter_not (G.inDarts i) (fun α => v (A (rev α)) = 1),
      ← hUdef, hα₀, Finset.prod_singleton, ← hk, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_congr rfl fun α _ => by field_simp
  have hβeq : β i = A (rev α₀) *
      ∏ α ∈ (G.inDarts i).filter (fun α => ¬ v (A (rev α)) = 1), A (rev α) / F i := by
    have hFp : F i ^ (G.degree i - 1) ≠ 0 := pow_ne_zero _ hF0
    have := hprod.symm.trans hsplit
    -- β * F^{d-1} = A₀ * (F^{d-1} * P)
    have h2 : (β i - A (rev α₀) * ∏ α ∈ (G.inDarts i).filter (fun α => ¬ v (A (rev α)) = 1),
        A (rev α) / F i) * F i ^ (G.degree i - 1) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · linear_combination h3
    · exact absurd h3 hFp
  have hβc : Cong v (β i) (-1) := by
    rw [hβeq]
    have h2 : Cong v (∏ α ∈ (G.inDarts i).filter (fun α => ¬ v (A (rev α)) = 1), A (rev α) / F i)
        (∏ _α ∈ (G.inDarts i).filter (fun α => ¬ v (A (rev α)) = 1), (1 : K)) :=
      Cong.prod _ _ _ (fun α hα => (val_eq_one_of_cong_one v (hUc α hα).2).le)
        (fun _ _ => by simp) (fun α hα => (hUc α hα).2)
    rw [Finset.prod_const_one] at h2
    have := Cong.mul (v := v) hα₀u.le (by simp) hα₀c h2
    rwa [mul_one] at this
  exact (val_add_one_eq_one_iff v (hβ i).le).1 (hβ1 i) hβc

/-- Section 4.4: if all F are units with residue different from -1, all A are units. -/
theorem val_A_eq_one (h : G.IsAuxSolution s β A F) (hs : ∀ e, v (s e - 1) < 1)
    (hFu : ∀ i, v (F i) = 1) (hF1 : ∀ i, v (1 + F i) = 1) (α : Dart E) : v (A α) = 1 := by
  have hα : rev α ∈ G.inDarts (G.tail α) := G.rev_mem_inDarts α
  have hq := quadratic_at h hα
  rw [rev_rev, rev_fst, tail_rev] at hq
  have hsu : v (s α.1) = 1 := val_eq_one_of_sub_one_lt v (hs α.1)
  have hratio : v ((1 + F (G.tail α)) / (1 + F (G.head α))) ≤ 1 := by
    rw [Valuation.map_div, hF1, hF1, div_one]
  have hH : v (1 - F (G.tail α) + (s α.1 - 1) * (1 - (1 + F (G.tail α)) / (1 + F (G.head α)))) ≤ 1 :=
    v.map_add_le ((v.map_sub 1 _).trans (max_le (by simp) (hFu _).le))
      (val_mul_lt_one_of_lt_of_le v (hs α.1) ((v.map_sub _ _).trans (max_le (by simp) hratio))).le
  exact val_eq_one_of_quadratic v hsu hH (hFu _) hq

/-- **Valuation form.** If s̄_e=1, β_i are units and β̄_i≠−1, every admissible auxiliary solution has unit F_i,A_{e,i} and F̄_i≠−1. -/
theorem boundary_exclusion (hs : ∀ e, v (s e - 1) < 1) (hβ : ∀ i, v (β i) = 1)
    (hβ1 : ∀ i, v (β i + 1) = 1) (h : G.IsAuxSolution s β A F) :
    (∀ i, v (F i) = 1) ∧ (∀ α, v (A α) = 1) ∧ (∀ i, v (F i + 1) = 1) := by
  have hs0 : ∀ e, s e ≠ 0 := fun e => ne_zero_of_val_eq_one v (val_eq_one_of_sub_one_lt v (hs e))
  have h' := isAuxSolution_flip (fun j => decide (1 < v (F j))) hs0 h
  have hs' := flipS_sub_one_lt (G := G) v (fun j => decide (1 < v (F j))) hs
  have hβ' := val_flipBeta (G := G) v (fun j => decide (1 < v (F j))) hs hβ
  have hβ1' := val_flipBeta_add_one (G := G) v (fun j => decide (1 < v (F j))) hs hβ hβ1
  have hF' : ∀ i, v (flipF (fun j => decide (1 < v (F j))) F i) ≤ 1 := val_flipF_le_one v F
  have hFu' := val_eq_one_of_le v h' hs' hβ' hβ1' hF'
  have hF1' := val_one_add_eq_one_of_le v h' hs' hβ' hβ1' hF'
  have hFu : ∀ i, v (F i) = 1 := fun i => val_eq_one_of_flipF v _ (hFu' i)
  have hF1 : ∀ i, v (F i + 1) = 1 := fun i =>
    val_add_one_eq_one_of_flipF v _ (hFu i) (by rw [add_comm]; exact hF1' i)
  exact ⟨hFu, fun α => val_A_eq_one v h hs hFu (fun i => by rw [add_comm]; exact hF1 i) α, hF1⟩

end Graph

end Multigraph

end BPFixedPoints
