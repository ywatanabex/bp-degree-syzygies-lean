import BPFixedPoints.Incidence.CechTensorCup

/-!
# Products on parity complexes and descent from arbitrary cocycles

Construct the product on contraction targets from an actual bilinear chain map
satisfying Leibniz. Prove the projection formula for arbitrary cocycles, as well
as the chosen representatives.
-/

namespace BPFixedPoints.GradedContraction

variable {R A B C H K L : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup H] [Module R H]
  [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]

theorem sign_sign_apply (a : GradedContraction R A H) (x : A) :
    a.sign (a.sign x) = x := LinearMap.congr_fun a.sign_sq x

theorem sign_d_apply (a : GradedContraction R A H) (x : A) :
    a.sign (a.d x) = -a.d (a.sign x) := LinearMap.congr_fun a.sign_d x

theorem d_sign_apply (a : GradedContraction R A H) (x : A) :
    a.d (a.sign x) = -a.sign (a.d x) := by rw [a.sign_d_apply, neg_neg]

theorem p_d_apply (a : GradedContraction R A H) (x : A) :
    a.p (a.d x) = 0 := LinearMap.congr_fun a.p_d x

/-- A product between three actual complexes preserving differentials and parity. -/
structure ChainPairing (a : GradedContraction R A H)
    (b : GradedContraction R B K) (c : GradedContraction R C L) where
  mul : A →ₗ[R] B →ₗ[R] C
  leibniz : ∀ x y, c.d (mul x y) = mul (a.d x) y + mul (a.sign x) (b.d y)
  sign_mul : ∀ x y, c.sign (mul x y) = mul (a.sign x) (b.sign y)

namespace ChainPairing

variable {a : GradedContraction R A H} {b : GradedContraction R B K}
  {c : GradedContraction R C L} (f : ChainPairing a b c)

theorem mul_cycles {x : A} {y : B} (hx : a.d x = 0) (hy : b.d y = 0) :
    c.d (f.mul x y) = 0 := by rw [f.leibniz, hx, hy]; simp

noncomputable def cycles : CyclePairing c H K where
  representative := f.mul.compl₁₂ a.i b.i
  closed x y := f.mul_cycles (LinearMap.congr_fun a.d_i x) (LinearMap.congr_fun b.d_i y)

noncomputable def cup : H →ₗ[R] K →ₗ[R] L := f.cycles.cup

theorem boundary_left (x : A) {y : B} (hy : b.d y = 0) :
    f.mul (a.d x) y = c.d (f.mul x y) := by rw [f.leibniz, hy]; simp

theorem boundary_right {x : A} (y : B) (hx : a.d x = 0) :
    f.mul x (b.d y) = c.d (f.mul (a.sign x) y) := by
  rw [f.leibniz, a.d_sign_apply, hx, map_zero, neg_zero, a.sign_sign_apply]
  simp

theorem cycle_decomposition {x : A} (hx : a.d x = 0) :
    x = a.d (a.h x) + a.i (a.p x) := by
  have h := LinearMap.congr_fun a.homotopy x
  change a.d (a.h x) + a.h (a.d x) + a.i (a.p x) = x at h
  simpa only [hx, map_zero, add_zero] using h.symm

/-- Any cocycle representatives compute the same product. -/
theorem cup_projection {x : A} {y : B} (hx : a.d x = 0) (hy : b.d y = 0) :
    f.cup (a.p x) (b.p y) = c.p (f.mul x y) := by
  have hleft : c.p (f.mul x y) = c.p (f.mul (a.i (a.p x)) y) := by
    nth_rw 1 [cycle_decomposition hx]
    rw [map_add, LinearMap.add_apply, map_add, f.boundary_left _ hy,
      c.p_d_apply, zero_add]
  rw [hleft]
  change c.p (f.mul (a.i (a.p x)) (b.i (b.p y))) = _
  nth_rw 2 [cycle_decomposition hy]
  rw [map_add, map_add, f.boundary_right _ (LinearMap.congr_fun a.d_i _),
    c.p_d_apply, zero_add]

theorem projection_eq_of_same_class {x x' : A} {y y' : B}
    (hx : a.d x = 0) (hx' : a.d x' = 0) (hy : b.d y = 0) (hy' : b.d y' = 0)
    (hxx : a.p x = a.p x') (hyy : b.p y = b.p y') :
    c.p (f.mul x y) = c.p (f.mul x' y') := by
  rw [← f.cup_projection hx hy, ← f.cup_projection hx' hy', hxx, hyy]

section Congr

variable {A' B' C' H' K' L' : Type*}
  [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
  [AddCommGroup C'] [Module R C'] [AddCommGroup H'] [Module R H']
  [AddCommGroup K'] [Module R K'] [AddCommGroup L'] [Module R L']

/-- Transfer to a contraction with the same differential and parity, retaining the product definition. -/
def rebase (a' : GradedContraction R A H') (b' : GradedContraction R B K')
    (c' : GradedContraction R C L')
    (ha : a'.d = a.d) (hb : b'.d = b.d) (hc : c'.d = c.d)
    (sa : a'.sign = a.sign) (sb : b'.sign = b.sign) (sc : c'.sign = c.sign) :
    ChainPairing a' b' c' where
  mul := f.mul
  leibniz x y := by rw [ha, hb, hc, sa]; exact f.leibniz x y
  sign_mul x y := by rw [sa, sb, sc]; exact f.sign_mul x y

noncomputable def congr (u : A ≃ₗ[R] A') (v : B ≃ₗ[R] B') (w : C ≃ₗ[R] C')
    (uH : H ≃ₗ[R] H') (vH : K ≃ₗ[R] K') (wH : L ≃ₗ[R] L') :
    ChainPairing (a.congr u uH) (b.congr v vH) (c.congr w wH) where
  mul := (f.mul.compl₁₂ u.symm.toLinearMap v.symm.toLinearMap).compr₂ w.toLinearMap
  leibniz x y := by
    change (c.congr w wH).d (w (f.mul (u.symm x) (v.symm y))) =
      w (f.mul (u.symm ((a.congr u uH).d x)) (v.symm y)) +
      w (f.mul (u.symm ((a.congr u uH).sign x)) (v.symm ((b.congr v vH).d y)))
    simp only [congr_d_apply, congr_sign_apply, LinearEquiv.symm_apply_apply,
      f.leibniz, map_add]
  sign_mul x y := by
    change (c.congr w wH).sign (w (f.mul (u.symm x) (v.symm y))) =
      w (f.mul (u.symm ((a.congr u uH).sign x)) (v.symm ((b.congr v vH).sign y)))
    simp only [congr_sign_apply, LinearEquiv.symm_apply_apply, f.sign_mul]

theorem congr_mul_apply (u : A ≃ₗ[R] A') (v : B ≃ₗ[R] B') (w : C ≃ₗ[R] C')
    (uH : H ≃ₗ[R] H') (vH : K ≃ₗ[R] K') (wH : L ≃ₗ[R] L') (x : A') (y : B') :
    (f.congr u v w uH vH wH).mul x y = w (f.mul (u.symm x) (v.symm y)) := rfl

theorem congr_cup_apply (u : A ≃ₗ[R] A') (v : B ≃ₗ[R] B') (w : C ≃ₗ[R] C')
    (uH : H ≃ₗ[R] H') (vH : K ≃ₗ[R] K') (wH : L ≃ₗ[R] L') (x : H') (y : K') :
    (f.congr u v w uH vH wH).cup x y = wH (f.cup (uH.symm x) (vH.symm y)) := by
  change (c.congr w wH).p (w (f.mul
    (u.symm ((a.congr u uH).i x)) (v.symm ((b.congr v vH).i y)))) = _
  simp only [congr_i_apply, congr_p_apply, LinearEquiv.symm_apply_apply]
  rfl

end Congr
end ChainPairing
end BPFixedPoints.GradedContraction
