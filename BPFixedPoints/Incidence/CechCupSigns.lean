import BPFixedPoints.Incidence.CechCupNaturality

/-! # Čech parity action for the total-complex product -/

namespace BPFixedPoints.CechProduct

open GradedContraction

variable (R : Type*) [CommRing R] {V : Type*} [Fintype V]

noncomputable def parity : Module.End R (C R V) := (contraction R (0 : V → ℕ)).sign

theorem parity_eq (d : V → ℕ) : parity R = (contraction R d).sign :=
  contraction_sign_twist R 0 d

@[simp] theorem parity_twice (x : C R V) : parity R (parity R x) = x :=
  (contraction R (0 : V → ℕ)).sign_sign_apply x

theorem parity_cup (d e : V → ℕ) (x y : C R V) :
    parity R (chainCup R d e x y) = chainCup R d e (parity R x) (parity R y) := by
  conv_lhs => rw [parity_eq R (d + e)]
  rw [chainCup_sign, ← parity_eq R d, ← parity_eq R e]

theorem parity_d (d : V → ℕ) (x : C R V) :
    parity R ((contraction R d).d x) = -(contraction R d).d (parity R x) := by
  rw [parity_eq R d]
  exact (contraction R d).sign_d_apply x

theorem d_parity_pow (d : V → ℕ) (n : ℕ) (x : C R V) :
    (contraction R d).d ((parity R ^ n) x) =
      (-1 : R) ^ n • (parity R ^ n) ((contraction R d).d x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, parity_eq R d,
      (contraction R d).d_sign_apply, ← parity_eq R d, ih,
      map_smul, pow_succ]
    simp only [mul_neg_one, neg_smul, smul_neg, Module.End.mul_apply]

theorem parity_pow_succ_apply (n : ℕ) (x : C R V) :
    (parity R ^ (n + 1)) x = parity R ((parity R ^ n) x) := by
  rw [pow_succ', Module.End.mul_apply]

theorem parity_pow_comm (n : ℕ) (x : C R V) :
    (parity R ^ n) (parity R x) = parity R ((parity R ^ n) x) := by
  rw [← Module.End.mul_apply, ← pow_succ, parity_pow_succ_apply]

theorem parity_pow_two_add (n : ℕ) :
    (parity R (V := V)) ^ (n + 2) = parity R ^ n := by
  apply LinearMap.ext
  intro x
  rw [show n + 2 = (n + 1) + 1 from rfl, parity_pow_succ_apply,
    parity_pow_succ_apply, parity_twice]

theorem parity_pow_single (n : ℕ) (b : V → Basis) (r : R) :
    (parity R ^ n) (Finsupp.single b r) =
      (-1 : R) ^ (cechDegree b * n) • Finsupp.single b r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [parity_pow_succ_apply, ih, map_smul, parity, contraction_sign_single,
      smul_smul, ← pow_add, Nat.mul_succ]

end BPFixedPoints.CechProduct
