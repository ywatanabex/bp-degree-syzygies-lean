import Mathlib

/-!
# Residue calculations in valued fields

For v:Valuation L Γ₀, with Γ₀ a linearly ordered commutative group with zero,
define `Cong v x y := v(x−y)<1`. Collect compatibility with ring operations,
inversion, powers and finite products; propagation of the unit condition v x=1;
the ultrametric fact that one term in a zero sum of three terms cannot have
strictly greatest valuation; and monotonicity of powers of p<1.
Using only valuations, rather than a residue-field map, makes boundary exclusion
applicable to arbitrary valued fields.
-/

namespace BPFixedPoints.BP

variable {L : Type*} [Field L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation L Γ₀)

/-- Equal residues: v(x-y)<1. -/
def Cong (x y : L) : Prop := v (x - y) < 1

namespace Cong

variable {v}

theorem refl (x : L) : Cong v x x := by simp [Cong]

theorem symm {x y : L} (h : Cong v x y) : Cong v y x := by
  unfold Cong at *; rwa [Valuation.map_sub_swap]

theorem trans {x y z : L} (hxy : Cong v x y) (hyz : Cong v y z) : Cong v x z := by
  unfold Cong at *
  have : x - z = (x - y) + (y - z) := by ring
  rw [this]
  exact lt_of_le_of_lt (v.map_add _ _) (max_lt hxy hyz)

theorem add {x x' y y' : L} (h1 : Cong v x x') (h2 : Cong v y y') : Cong v (x + y) (x' + y') := by
  unfold Cong at *
  have : x + y - (x' + y') = (x - x') + (y - y') := by ring
  rw [this]
  exact lt_of_le_of_lt (v.map_add _ _) (max_lt h1 h2)

theorem neg {x y : L} (h : Cong v x y) : Cong v (-x) (-y) := by
  unfold Cong at *
  rwa [show -x - -y = -(x - y) by ring, Valuation.map_neg]

theorem sub {x x' y y' : L} (h1 : Cong v x x') (h2 : Cong v y y') : Cong v (x - y) (x' - y') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact h1.add h2.neg

/-- An element congruent to a unit is a unit. -/
theorem val_eq_one {x y : L} (h : Cong v x y) (hy : v y = 1) : v x = 1 := by
  have := v.map_eq_of_sub_lt (x := y) (y := x) (by rw [hy]; exact h)
  rw [this, hy]

theorem val_le_one {x y : L} (h : Cong v x y) (hy : v y ≤ 1) : v x ≤ 1 := by
  have : x = (x - y) + y := by ring
  rw [this]
  exact v.map_add_le h.le hy

theorem val_lt_one {x y : L} (h : Cong v x y) (hy : v y < 1) : v x < 1 := by
  have : x = (x - y) + y := by ring
  rw [this]
  exact lt_of_le_of_lt (v.map_add _ _) (max_lt h hy)

theorem mul {x x' y y' : L} (hx : v x ≤ 1) (hy' : v y' ≤ 1) (h1 : Cong v x x') (h2 : Cong v y y') :
    Cong v (x * y) (x' * y') := by
  unfold Cong at *
  have : x * y - x' * y' = x * (y - y') + (x - x') * y' := by ring
  rw [this]
  refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
  · rw [Valuation.map_mul]
    calc v x * v (y - y') ≤ 1 * v (y - y') := by gcongr
      _ = v (y - y') := one_mul _
      _ < 1 := h2
  · rw [Valuation.map_mul]
    calc v (x - x') * v y' ≤ v (x - x') * 1 := by gcongr
      _ = v (x - x') := mul_one _
      _ < 1 := h1

theorem inv {x y : L} (hx : v x = 1) (hy : v y = 1) (h : Cong v x y) : Cong v x⁻¹ y⁻¹ := by
  unfold Cong at *
  have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hx
  have hy0 : y ≠ 0 := fun h0 => by simp [h0] at hy
  have : x⁻¹ - y⁻¹ = (y - x) / (x * y) := by field_simp
  rw [this, Valuation.map_div, Valuation.map_mul, hx, hy, one_mul, div_one,
    Valuation.map_sub_swap]
  exact h

theorem pow {x y : L} (hx : v x ≤ 1) (hy : v y ≤ 1) (h : Cong v x y) (n : ℕ) :
    Cong v (x ^ n) (y ^ n) := by
  induction n with
  | zero => simp [refl]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul (by rw [Valuation.map_pow]; exact pow_le_one₀ zero_le hx) hy h

theorem zpow {x y : L} (hx : v x = 1) (hy : v y = 1) (h : Cong v x y) (n : ℤ) :
    Cong v (x ^ n) (y ^ n) := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast, zpow_natCast]; exact h.pow hx.le hy.le m
  · rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
    exact (h.pow hx.le hy.le m).inv (by rw [Valuation.map_pow, hx, one_pow])
      (by rw [Valuation.map_pow, hy, one_pow])

theorem prod {ι : Type*} (s : Finset ι) (f g : ι → L) (hf : ∀ i ∈ s, v (f i) ≤ 1)
    (hg : ∀ i ∈ s, v (g i) ≤ 1) (h : ∀ i ∈ s, Cong v (f i) (g i)) :
    Cong v (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [refl]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine Cong.mul (hf a (Finset.mem_insert_self a s)) ?_
      (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    rw [map_prod]
    exact Finset.prod_le_one fun i hi => hg i (Finset.mem_insert_of_mem hi)

end Cong

/-- Residue -1 is equivalent to v(x+1)<1. -/
theorem cong_neg_one_iff {x : L} : Cong v x (-1) ↔ v (x + 1) < 1 := by
  unfold Cong; rw [sub_neg_eq_add]

/-- Residue 1 is equivalent to v(x-1)<1. -/
theorem cong_one_iff {x : L} : Cong v x 1 ↔ v (x - 1) < 1 := Iff.rfl

theorem val_eq_one_of_cong_neg_one {x : L} (h : Cong v x (-1)) : v x = 1 :=
  h.val_eq_one (by simp)

theorem val_eq_one_of_cong_one {x : L} (h : Cong v x 1) : v x = 1 :=
  h.val_eq_one (by simp)

/-- For integral x, v(x+1)≤1. -/
theorem val_add_one_le_one {x : L} (hx : v x ≤ 1) : v (x + 1) ≤ 1 :=
  v.map_add_le hx (by simp)

/-- For integral x, v(x+1)=1 exactly when its residue is not -1. -/
theorem val_add_one_eq_one_iff {x : L} (hx : v x ≤ 1) : v (x + 1) = 1 ↔ ¬ Cong v x (-1) := by
  rw [cong_neg_one_iff]
  constructor
  · intro h h'; rw [h] at h'; exact lt_irrefl _ h'
  · intro h; exact le_antisymm (val_add_one_le_one v hx) (not_lt.1 h)

/-- Ultrametric exclusion: x+y=0 cannot hold if v(y)<v(x). -/
theorem two_term_contra {x y : L} (h : x + y = 0) (hy : v y < v x) : False := by
  have : x = -y := by linear_combination h
  rw [this, Valuation.map_neg] at hy
  exact lt_irrefl _ hy

/-- Ultrametric exclusion: x+y+z=0 cannot hold if both v(y),v(z)<v(x). -/
theorem three_term_contra {x y z : L} (h : x + y + z = 0) (hy : v y < v x) (hz : v z < v x) :
    False := by
  have : x = -(y + z) := by linear_combination h
  have h2 : v x ≤ max (v y) (v z) := by rw [this, Valuation.map_neg]; exact v.map_add _ _
  exact lt_irrefl _ (lt_of_le_of_lt h2 (max_lt hy hz))

/-- If 0<p<1 and n≥1, then p^n<1. -/
theorem pow_lt_one_of_lt_one {p : Γ₀} (hp : p < 1) {n : ℕ} (hn : n ≠ 0) : p ^ n < 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  calc p ^ (m + 1) = p * p ^ m := by rw [pow_succ, mul_comm]
    _ ≤ p * 1 := by gcongr; exact pow_le_one₀ zero_le hp.le
    _ = p := mul_one p
    _ < 1 := hp

/-- If 0<p<1 and p^m=p^n, then m=n. -/
theorem pow_right_injective_of_lt_one {p : Γ₀} (hp0 : p ≠ 0) (hp : p < 1) {m n : ℕ}
    (h : p ^ m = p ^ n) : m = n := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have : p ^ n = p ^ m * p ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [this] at h
    have hpos : 0 < p ^ m := pow_pos (lt_of_le_of_ne zero_le (Ne.symm hp0)) m
    have hlt' : p ^ m * p ^ (n - m) < p ^ m * 1 :=
      mul_lt_mul_of_pos_left (pow_lt_one_of_lt_one hp (by omega)) hpos
    rw [mul_one, ← h] at hlt'
    exact lt_irrefl _ hlt'
  · have : p ^ m = p ^ n * p ^ (m - n) := by rw [← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [this] at h
    have hpos : 0 < p ^ n := pow_pos (lt_of_le_of_ne zero_le (Ne.symm hp0)) n
    have hlt' : p ^ n * p ^ (m - n) < p ^ n * 1 :=
      mul_lt_mul_of_pos_left (pow_lt_one_of_lt_one hp (by omega)) hpos
    rw [mul_one, h] at hlt'
    exact lt_irrefl _ hlt'

/-- A product of units is a unit. -/
theorem val_mul_eq_one {x y : L} (hx : v x = 1) (hy : v y = 1) : v (x * y) = 1 := by
  rw [Valuation.map_mul, hx, hy, one_mul]

theorem val_prod_eq_one {ι : Type*} (s : Finset ι) (f : ι → L) (hf : ∀ i ∈ s, v (f i) = 1) :
    v (∏ i ∈ s, f i) = 1 := by
  rw [map_prod]; exact Finset.prod_eq_one hf

/-- If v(x)<1 and v(y)≤1, then v(xy)<1. -/
theorem val_mul_lt_one_of_lt_of_le {x y : L} (hx : v x < 1) (hy : v y ≤ 1) : v (x * y) < 1 := by
  rw [Valuation.map_mul]
  calc v x * v y ≤ v x * 1 := by gcongr
    _ = v x := mul_one _
    _ < 1 := hx

theorem val_mul_le_one {x y : L} (hx : v x ≤ 1) (hy : v y ≤ 1) : v (x * y) ≤ 1 := by
  rw [Valuation.map_mul]
  calc v x * v y ≤ 1 * 1 := mul_le_mul' hx hy
    _ = 1 := one_mul _

/-- If v(x)=1, then x≠0. -/
theorem ne_zero_of_val_eq_one {x : L} (hx : v x = 1) : x ≠ 0 := fun h => by simp [h] at hx

/-- If v(x)<1 and v(y)=1, then v(x+y)=1. -/
theorem val_add_eq_one_of_lt {x y : L} (hx : v x < 1) (hy : v y = 1) : v (x + y) = 1 := by
  rw [v.map_add_eq_of_lt_right (by rw [hy]; exact hx), hy]

end BPFixedPoints.BP
