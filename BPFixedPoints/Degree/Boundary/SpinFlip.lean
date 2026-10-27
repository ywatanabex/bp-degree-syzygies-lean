import BPFixedPoints.Degree.AuxSystem
import BPFixedPoints.Degree.Boundary.ResidueCalc

/-!
# Spin reversal

Choose σ_i∈{+1,−1} and exchange spin labels where σ_i=−1. In auxiliary coordinates,
F'_i=F_i^{σ_i}, s'_e=s_e^{σ_iσ_j},
A'_{e,i}=s_e^{σ_i(1−σ_j)/2}A_{e,i}^{σ_i},
β'_i=β_i^{σ_i}∏_{e=ij,σ_j=−1}s_e^{σ_i} (10).
This preserves solutions (`isAuxSolution_flip`). Encode flips by V→Bool,
with true meaning reversal and `flipVal true x=x⁻¹`.
Over a valued field it preserves s̄_e=1, unit β_i and β̄_i≠−1. Flipping exactly
vertices with v(F_i)>1 makes every F'_i integral.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace BP

variable {K : Type*} [Field K]

/-- `flipVal true x = x⁻¹`、`flipVal false x = x`。 -/
def flipVal (b : Bool) (x : K) : K := if b then x⁻¹ else x

@[simp] theorem flipVal_false (x : K) : flipVal false x = x := rfl
@[simp] theorem flipVal_true (x : K) : flipVal true x = x⁻¹ := rfl

theorem flipVal_mul (b : Bool) (x y : K) : flipVal b (x * y) = flipVal b x * flipVal b y := by
  cases b
  · rfl
  · exact mul_inv x y

theorem flipVal_ne_zero (b : Bool) {x : K} (hx : x ≠ 0) : flipVal b x ≠ 0 := by
  cases b <;> simp [flipVal, hx]

theorem flipVal_prod (b : Bool) {ι : Type*} (s : Finset ι) (f : ι → K) :
    flipVal b (∏ i ∈ s, f i) = ∏ i ∈ s, flipVal b (f i) := by
  cases b <;> simp [flipVal, Finset.prod_inv_distrib]

theorem flipVal_zpow (b : Bool) (x : K) (n : ℤ) : flipVal b (x ^ n) = flipVal b x ^ n := by
  cases b
  · rfl
  · exact (inv_zpow x n).symm

theorem flipVal_flipVal (b : Bool) (x : K) : flipVal b (flipVal b x) = x := by
  cases b <;> simp [flipVal]

theorem flipVal_ne_neg_one (b : Bool) {x : K} (hx : x ≠ -1) : flipVal b x ≠ -1 := by
  cases b
  · simpa using hx
  · simp only [flipVal_true]
    intro h
    apply hx
    rw [← inv_inv x, h]; norm_num

end BP

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)
variable {K : Type*} [Field K]

/-- Transformed s'_e=s_e^{σ_iσ_j}: retain s_e when endpoint flips agree and invert it otherwise. -/
def flipS (σ : V → Bool) (s : E → K) (e : E) : K :=
  if σ (G.fst e) = σ (G.snd e) then s e else (s e)⁻¹

/-- The s-factor s_e^{σ_i(1-σ_j)/2} for the auxiliary coordinate at the tail of γ. -/
def flipFactor (σ : V → Bool) (s : E → K) (γ : Dart E) : K :=
  if σ (G.head γ) then (if σ (G.tail γ) then (s γ.1)⁻¹ else s γ.1) else 1

/-- Transformed auxiliary coordinate at the tail of γ. -/
def flipA (σ : V → Bool) (s : E → K) (A : Dart E → K) (γ : Dart E) : K :=
  G.flipFactor σ s γ * flipVal (σ (G.tail γ)) (A γ)

/-- Transformed full field F'_i=F_i^{σ_i}, independently of the graph. -/
def flipF (σ : V → Bool) (F : V → K) (i : V) : K := flipVal (σ i) (F i)

/-- Transformed β'_i=β_i^{σ_i} product_{e=ij,σ_j=-1} s_e^{σ_i}. -/
def flipBeta (σ : V → Bool) (s : E → K) (β : V → K) (i : V) : K :=
  flipVal (σ i) (β i) *
    ∏ α ∈ (G.inDarts i).filter (fun α => σ (G.tail α)), flipVal (σ i) (s α.1)

variable {G}

theorem flipS_eq (σ : V → Bool) (s : E → K) (α : Dart E) :
    G.flipS σ s α.1 = if σ (G.tail α) = σ (G.head α) then s α.1 else (s α.1)⁻¹ := by
  rcases α with ⟨e, _ | _⟩
  · simp only [flipS, tail, head, Bool.cond_false, Bool.cond_true]
    by_cases h : σ (G.fst e) = σ (G.snd e)
    · simp [h]
    · simp [h, Ne.symm h]
  · rfl

theorem flipFactor_rev (σ : V → Bool) (s : E → K) {i : V} {α : Dart E} (hα : α ∈ G.inDarts i) :
    G.flipFactor σ s (rev α) = if σ (G.tail α) then flipVal (σ i) (s α.1) else 1 := by
  rw [inDarts, Finset.mem_filter] at hα
  unfold flipFactor
  rw [head_rev, tail_rev, hα.2, rev_fst]
  cases σ (G.tail α) <;> cases σ i <;> simp [flipVal]

theorem flipFactor_ne_zero (σ : V → Bool) {s : E → K} (hs : ∀ e, s e ≠ 0) (γ : Dart E) :
    G.flipFactor σ s γ ≠ 0 := by
  unfold flipFactor
  split_ifs <;> simp [hs]

section Transform

variable {s : E → K} {β : V → K} {A : Dart E → K} {F : V → K}

/-- Spin reversal sends solutions of the auxiliary system to solutions. -/
theorem isAuxSolution_flip (σ : V → Bool) (hs : ∀ e, s e ≠ 0) (h : G.IsAuxSolution s β A F) :
    G.IsAuxSolution (G.flipS σ s) (G.flipBeta σ s β) (G.flipA σ s A) (flipF σ F) where
  A_ne_zero γ := mul_ne_zero (flipFactor_ne_zero σ hs γ) (flipVal_ne_zero _ (h.A_ne_zero γ))
  A_ne_neg_one γ := by
    have hsA : 1 + s γ.1 * A γ ≠ 0 := by
      have h2 := h.edge (rev γ)
      rw [tail_rev, rev_rev, rev_fst] at h2
      exact BP.one_add_s_mul_ne_zero h2 (h.F_ne_zero _)
        (fun h0 => h.A_ne_neg_one γ (by linear_combination h0))
    have hA := h.A_ne_neg_one γ
    have hA0 := h.A_ne_zero γ
    have hs' := hs γ.1
    unfold flipA flipFactor
    cases hh : σ (G.head γ) <;> cases ht : σ (G.tail γ) <;> simp only [flipVal, ite_true, ite_false,
      Bool.false_eq_true, one_mul]
    · exact hA
    · intro h0; apply hA; rw [← inv_inv (A γ), h0]; norm_num
    · intro h0; apply hsA; linear_combination h0
    · intro h0; apply hsA
      have : (s γ.1 * A γ)⁻¹ = -1 := by rw [mul_inv]; exact h0
      rw [← inv_inv (s γ.1 * A γ), this]; norm_num
  F_ne_zero i := flipVal_ne_zero _ (h.F_ne_zero i)
  F_ne_neg_one i := flipVal_ne_neg_one _ (h.F_ne_neg_one i)
  edge α := by
    have he := h.edge α
    have hF := h.F_ne_zero (G.tail α)
    have ha := h.A_ne_zero α
    have hb := h.A_ne_zero (rev α)
    have hs' := hs α.1
    unfold flipF flipA flipFactor
    rw [flipS_eq, head_rev, tail_rev, rev_fst]
    cases ht : σ (G.tail α) <;> cases hh : σ (G.head α) <;>
      simp only [flipVal, ite_true, ite_false, Bool.false_eq_true, one_mul, Bool.true_eq_false]
    · exact he
    · field_simp
      linear_combination he
    · field_simp
      linear_combination -he
    · field_simp
      linear_combination -he
  vertex i := by
    have hprod : ∏ α ∈ G.inDarts i, G.flipFactor σ s (rev α) =
        ∏ α ∈ (G.inDarts i).filter (fun α => σ (G.tail α)), flipVal (σ i) (s α.1) := by
      rw [Finset.prod_filter]
      exact Finset.prod_congr rfl fun α hα => flipFactor_rev σ s hα
    have hA' : ∀ α ∈ G.inDarts i, G.flipA σ s A (rev α) =
        G.flipFactor σ s (rev α) * flipVal (σ i) (A (rev α)) := by
      intro α hα
      rw [inDarts, Finset.mem_filter] at hα
      unfold flipA
      rw [tail_rev, hα.2]
    unfold flipBeta flipF
    rw [h.vertex i, Finset.prod_congr rfl hA', Finset.prod_mul_distrib, hprod, flipVal_mul,
      flipVal_zpow, flipVal_prod]
    ring

end Transform

section Valuation

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
variable {s : E → K} {β : V → K} {F : V → K}

theorem val_eq_one_of_sub_one_lt {x : K} (hx : v (x - 1) < 1) : v x = 1 := by
  have := v.map_one_add_of_lt hx
  rwa [add_sub_cancel] at this

theorem val_flipVal (b : Bool) {x : K} (hx : v x = 1) : v (flipVal b x) = 1 := by
  cases b <;> simp [flipVal, hx]

/-- Inverting an element with residue 1 preserves residue 1. -/
theorem cong_flipVal_one (b : Bool) {x : K} (hx : Cong v x 1) : Cong v (flipVal b x) 1 := by
  cases b
  · simpa using hx
  · simp only [flipVal_true]
    have := hx.inv (val_eq_one_of_cong_one v hx) (by simp)
    rwa [inv_one] at this

/-- Inverting a unit whose residue differs from -1 preserves that property. -/
theorem not_cong_flipVal_neg_one (b : Bool) {x : K} (hx : v x = 1) (h : ¬ Cong v x (-1)) :
    ¬ Cong v (flipVal b x) (-1) := by
  cases b
  · simpa using h
  · simp only [flipVal_true]
    intro h'
    apply h
    have := h'.inv (by rw [Valuation.map_inv, hx, inv_one]) (by simp)
    rwa [inv_inv, inv_neg, inv_one] at this

/-- Residue s_e=1 is preserved by a flip. -/
theorem flipS_sub_one_lt (σ : V → Bool) (hs : ∀ e, v (s e - 1) < 1) (e : E) :
    v (G.flipS σ s e - 1) < 1 := by
  unfold flipS
  split_ifs
  · exact hs e
  · exact cong_flipVal_one v true (hs e)

/-- Transformed β is a unit. -/
theorem val_flipBeta (σ : V → Bool) (hs : ∀ e, v (s e - 1) < 1) (hβ : ∀ i, v (β i) = 1) (i : V) :
    v (G.flipBeta σ s β i) = 1 := by
  unfold flipBeta
  rw [Valuation.map_mul, val_flipVal v _ (hβ i), one_mul]
  apply val_prod_eq_one
  intro α _
  exact val_flipVal v _ (val_eq_one_of_sub_one_lt v (hs α.1))

/-- The transformed β still has residue different from -1. -/
theorem val_flipBeta_add_one (σ : V → Bool) (hs : ∀ e, v (s e - 1) < 1) (hβ : ∀ i, v (β i) = 1)
    (hβ1 : ∀ i, v (β i + 1) = 1) (i : V) : v (G.flipBeta σ s β i + 1) = 1 := by
  rw [val_add_one_eq_one_iff v (val_flipBeta v σ hs hβ i).le]
  have hβ' : ¬ Cong v (flipVal (σ i) (β i)) (-1) :=
    not_cong_flipVal_neg_one v _ (hβ i) ((val_add_one_eq_one_iff v (hβ i).le).1 (hβ1 i))
  intro hc
  apply hβ'
  -- flipBeta ≡ flipVal β · ∏ 1 = flipVal β
  have hP : Cong v (∏ α ∈ (G.inDarts i).filter (fun α => σ (G.tail α)), flipVal (σ i) (s α.1)) 1 := by
    have := Cong.prod (v := v) ((G.inDarts i).filter (fun α => σ (G.tail α)))
      (fun α => flipVal (σ i) (s α.1)) (fun _ => 1)
      (fun α _ => (val_flipVal v _ (val_eq_one_of_sub_one_lt v (hs α.1))).le)
      (fun _ _ => by simp)
      (fun α _ => cong_flipVal_one v _ (hs α.1))
    simpa using this
  have hmul : Cong v (G.flipBeta σ s β i) (flipVal (σ i) (β i)) := by
    unfold flipBeta
    have := Cong.mul (v := v) (val_flipVal v _ (hβ i)).le (by simp)
      (Cong.refl (flipVal (σ i) (β i))) hP
    simpa using this
  exact hmul.symm.trans hc

/-- Flipping precisely the vertices with poles makes all transformed full fields integral. -/
theorem val_flipF_le_one (F : V → K) (i : V) :
    v (flipF (fun j => decide (1 < v (F j))) F i) ≤ 1 := by
  unfold flipF
  by_cases h : 1 < v (F i)
  · simp only [h, decide_true, flipVal_true, Valuation.map_inv]
    exact (inv_le_one₀ (lt_trans zero_lt_one h)).2 h.le
  · simp only [h, decide_false, flipVal_false]
    exact not_lt.1 h

/-- If the transformed full fields are units, the original full fields are units. -/
theorem val_eq_one_of_flipF (σ : V → Bool) {F : V → K} {i : V} (h : v (flipF σ F i) = 1) :
    v (F i) = 1 := by
  unfold flipF at h
  cases hσ : σ i
  · rw [hσ] at h; simpa using h
  · rw [hσ] at h; simp only [flipVal_true, Valuation.map_inv] at h
    rwa [inv_eq_one] at h

/-- If transformed full-field residues differ from -1, so do the original residues. -/
theorem val_add_one_eq_one_of_flipF (σ : V → Bool) {F : V → K} {i : V} (hF : v (F i) = 1)
    (h : v (flipF σ F i + 1) = 1) : v (F i + 1) = 1 := by
  unfold flipF at h
  rw [val_add_one_eq_one_iff v hF.le]
  rw [val_add_one_eq_one_iff v (val_flipVal v _ hF).le] at h
  exact fun hc => h (by
    cases hσ : σ i
    · simpa using hc
    · simp only [flipVal_true]
      have := hc.inv hF (by simp)
      rwa [inv_neg, inv_one] at this)

end Valuation

end Multigraph

end BPFixedPoints
