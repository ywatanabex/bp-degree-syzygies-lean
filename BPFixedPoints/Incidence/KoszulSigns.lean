import BPFixedPoints.Incidence.KoszulLinear

/-! # Agreement of Koszul signs over different coefficient rings -/

namespace BPFixedPoints.Koszul

variable {R A M N : Type*} [CommRing R] [CommRing A]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module A N]

theorem map_neg_one_pow_smul (f : M →+ N) (n : ℕ) (x : M) :
    f ((-1 : R) ^ n • x) = (-1 : A) ^ n • f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, neg_one_smul, map_neg, ih,
      pow_succ', mul_smul, neg_one_smul]

theorem map_sign_smul {E : Type*} [LinearOrder E]
    (f : M →+ N) (S : Finset E) (e : E) (x : M) :
    f (sign (A := R) S e • x) = sign (A := A) S e • f x :=
  map_neg_one_pow_smul f (index S e) x

theorem differential_single {E : Type*} [LinearOrder E] [Fintype E]
    (f : E → A) (S : Finset E) (x : A) :
    differential f (Finsupp.single S x) =
      ∑ e ∈ S, Finsupp.single (S.erase e) (sign S e * (f e * x)) := by
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply, erase_single,
    smul_ite, smul_zero, Finsupp.smul_single, smul_eq_mul]
  simp_rw [mul_left_comm (f _) (sign S _)]
  rw [← Finset.sum_filter]
  simp

end BPFixedPoints.Koszul
