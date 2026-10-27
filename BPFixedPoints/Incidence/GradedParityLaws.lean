import BPFixedPoints.Incidence.GradedFreeTensor

/-! # Parity on homogeneous parts of free complexes -/
namespace BPFixedPoints.ResolutionTools
open Finsupp
universe u
variable {R A : Type u} [CommRing R] (degree : A → ℕ)

theorem gradedParity_homogeneous (p : ℕ) {x : A →₀ R}
    (hx : x ∈ gradedPiece R degree p) : gradedParity degree x = (-1 : R) ^ p • x := by
  ext a
  rw [gradedParity_apply, Finsupp.smul_apply, smul_eq_mul]
  by_cases h : degree a = p
  · rw [h]
  · rw [(mem_supported' R x).mp hx a h]
    simp

theorem gradedParity_zero {x : A →₀ R} (hx : x ∈ gradedPiece R degree 0) :
    gradedParity degree x = x := by
  rw [gradedParity_homogeneous degree 0 hx]
  simp

theorem gradedParity_twice (x : A →₀ R) : gradedParity degree (gradedParity degree x) = x := by
  ext a
  rw [gradedParity_apply, gradedParity_apply, ← mul_assoc, ← mul_pow]
  simp

theorem gradedParity_pow_two_add (n : ℕ) :
    (gradedParity (R := R) degree) ^ (n + 2) = gradedParity degree ^ n := by
  apply LinearMap.ext
  intro x
  rw [show n + 2 = (n + 1) + 1 from rfl, pow_succ', Module.End.mul_apply,
    pow_succ', Module.End.mul_apply, gradedParity_twice]

theorem gradedParity_pow_homogeneous (n p : ℕ) {x : A →₀ R}
    (hx : x ∈ gradedPiece R degree p) :
    (gradedParity degree ^ n) x = (-1 : R) ^ (n * p) • x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul,
      gradedParity_homogeneous degree p hx, smul_smul, ← pow_add]
    simp only [Nat.succ_mul, Nat.one_mul]

variable (D : Module.End R (A →₀ R))
  (hd : HasDegree (fun a => (degree a : ℤ)) (fun a => (degree a : ℤ)) (-1) D)

include hd in
theorem d_gradedParity (x : A →₀ R) :
    D (gradedParity degree x) = -gradedParity degree (D x) := by
  have h := congrArg Neg.neg (LinearMap.congr_fun (gradedParity_d degree D hd) x).symm
  simpa only [Module.End.mul_apply, LinearMap.neg_apply, neg_neg] using h

include hd in
theorem d_gradedParity_pow (n : ℕ) (x : A →₀ R) :
    D ((gradedParity degree ^ n) x) = (-1 : R) ^ n • (gradedParity degree ^ n) (D x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, d_gradedParity degree D hd,
      ih, map_smul, pow_succ]
    simp only [mul_neg_one, neg_smul, smul_neg, Module.End.mul_apply]

include hd in
theorem differential_zero_degree {x : A →₀ R} (hx : x ∈ gradedPiece R degree 0) : D x = 0 := by
  have hx' : x ∈ supported R R {a | (degree a : ℤ) = 0} := by
    simpa only [gradedPiece, Int.natCast_eq_zero] using hx
  have h := hd 0 x hx'
  ext a
  apply (mem_supported' R _).mp h a
  change (degree a : ℤ) ≠ 0 + -1
  omega

end BPFixedPoints.ResolutionTools
