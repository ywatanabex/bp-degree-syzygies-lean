import BPFixedPoints.Degree.Lift.Taylor
import BPFixedPoints.Degree.Boundary.ResidueCalc

/-!
# Uniqueness of roots with the same residue over a valued field

For a polynomial system over the valuation ring and roots x,x' with the
same residue, assume the Jacobian determinant at x is a unit. Put h=x'-x
and m=max_j v(h_j)<1. Taylor expansion gives v(J(x)h)≤m².
The inverse Jacobian has integral entries, hence v(h_j)≤m² and m≤m²,
which forces m=0. No completeness or Puiseux expansions are needed.
This supplies uniqueness in the full Puiseux-type root count.
-/

namespace BPFixedPoints.BP

open MvPolynomial

variable {L : Type*} [Field L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation L Γ₀) {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Over the valuation ring, an element of the quadratic ideal has valuation at most (max_j v(h_j))². -/
theorem val_le_of_mem_quadIdeal {h : ι → v.integer} {m : Γ₀} (hh : ∀ j, v (h j : L) ≤ m)
    {r : v.integer} (hr : r ∈ quadIdeal h) : v (r : L) ≤ m * m := by
  unfold quadIdeal at hr
  induction hr using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨j, k⟩, rfl⟩ := hy
    simp only [Subring.coe_mul, Valuation.map_mul]
    exact mul_le_mul' (hh j) (hh k)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [Subring.coe_add]
    exact v.map_add_le hy hz
  | smul a y _ hy =>
    rw [smul_eq_mul, Subring.coe_mul, Valuation.map_mul]
    calc v (a : L) * v (y : L) ≤ 1 * (m * m) := mul_le_mul' a.2 hy
      _ = m * m := one_mul _

/-- An integral matrix-vector product has valuation at most the maximum valuation of the vector components. -/
theorem val_mulVec_le (M : Matrix ι ι v.integer) (w : ι → v.integer) {m : Γ₀}
    (hw : ∀ j, v (w j : L) ≤ m) (i : ι) : v ((M.mulVec w) i : L) ≤ m := by
  simp only [Matrix.mulVec, dotProduct]
  change v (v.integer.subtype _) ≤ m
  rw [map_sum]
  apply v.map_sum_le
  intro j _
  rw [map_mul, Valuation.map_mul]
  calc v (v.integer.subtype (M i j)) * v (v.integer.subtype (w j)) ≤ 1 * m :=
        mul_le_mul' (M i j).2 (hw j)
    _ = m := one_mul _

/-- Two roots with the same residue coincide when the Jacobian determinant is a unit. -/
theorem unique_of_cong {f : ι → MvPolynomial ι v.integer} {x x' : ι → v.integer}
    (hx : ∀ i, eval x (f i) = 0) (hx' : ∀ i, eval x' (f i) = 0)
    (hcong : ∀ j, v ((x' j - x j : v.integer) : L) < 1)
    (hJ : v (((Matrix.of fun i j => eval x (pderiv j (f i))).det : v.integer) : L) = 1) :
    x = x' := by
  set J : Matrix ι ι v.integer := Matrix.of fun i j => eval x (pderiv j (f i)) with hJdef
  set h : ι → v.integer := x' - x with hhdef
  have hJu : IsUnit J.det := Valuation.Integers.isUnit_of_one' (Valuation.integer.integers v) hJ
  -- m = max_j v (h j)
  set m : Γ₀ := Finset.univ.sup fun j => v (h j : L) with hmdef
  have hhm : ∀ j, v (h j : L) ≤ m := fun j => Finset.le_sup (f := fun j => v (h j : L)) (Finset.mem_univ j)
  have hbot : (⊥ : Γ₀) < 1 := by
    refine lt_of_le_of_ne bot_le ?_
    intro h
    have h1 : (1 : Γ₀) ≤ 0 := h ▸ bot_le
    exact absurd h1 (not_le.2 zero_lt_one)
  have hm1 : m < 1 := by
    rw [hmdef, Finset.sup_lt_iff hbot]
    intro j _
    exact hcong j
  -- Componentwise, J h belongs to quadIdeal h.
  have hJh : ∀ i, v ((J.mulVec h) i : L) ≤ m * m := by
    intro i
    have ht := taylor_first_order (f i) x h
    rw [show x + h = x' by simp [hhdef], hx' i, hx i, sub_zero, zero_sub] at ht
    have hs : (J.mulVec h) i = ∑ j, eval x (pderiv j (f i)) * h j := by
      simp [hJdef, Matrix.mulVec, dotProduct]
    rw [hs]
    have := val_le_of_mem_quadIdeal v hhm ht
    rwa [Subring.coe_neg, Valuation.map_neg] at this
  -- h = J⁻¹ (J h)
  have hinv : h = J⁻¹.mulVec (J.mulVec h) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hJu, Matrix.one_mulVec]
  have hbound : ∀ j, v (h j : L) ≤ m * m := by
    intro j
    rw [hinv]
    exact val_mulVec_le v J⁻¹ (J.mulVec h) hJh j
  have hmm : m ≤ m * m := by
    rw [hmdef]
    exact Finset.sup_le fun j _ => by rw [← hmdef]; exact hbound j
  have hm0 : m = 0 := by
    by_contra hne
    have hpos : 0 < m := lt_of_le_of_ne zero_le (Ne.symm hne)
    have : m * m < m * 1 := mul_lt_mul_of_pos_left hm1 hpos
    rw [mul_one] at this
    exact lt_irrefl _ (lt_of_le_of_lt hmm this)
  funext j
  have h0 : v (h j : L) = 0 := le_antisymm (hm0 ▸ hhm j) zero_le
  have : (h j : L) = 0 := (Valuation.zero_iff v).1 h0
  have hj : h j = 0 := Subtype.ext this
  rw [hhdef, Pi.sub_apply, sub_eq_zero] at hj
  exact hj.symm

end BPFixedPoints.BP
