import BPFixedPoints.Incidence.CechChainCupComparison
import BPFixedPoints.Incidence.CechProductMaps

/-!
# Basis formula for the multi-vertex Čech chain product

Reduce the monomial formula for the full product to the four nonzero local
Alexander–Whitney terms.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace BPFixedPoints.CechProduct

open Finsupp GradedContraction
open scoped TensorProduct

variable (R : Type*) [CommRing R]

def lineCupBasis (e : ℕ) : Basis → Basis → Option Basis
  | .inl a, .inl b => some (.inl (a + b))
  | .inr (.inl a), .inr (.inl b) => some (.inr (.inl (a + b)))
  | .inl a, .inr (.inr b) => some (.inr (.inr ((a : ℤ) + b)))
  | .inr (.inr a), .inr (.inl b) => some (.inr (.inr (a + (-(e : ℤ) - b))))
  | _, _ => none

theorem lineCupBasis_degree (e : ℕ) {a b c : Basis} (h : lineCupBasis e a b = some c) :
    lineDegree c = lineDegree a + lineDegree b := by
  rcases a with a | a | a <;> rcases b with b | b | b <;>
    simp only [lineCupBasis, Option.some.injEq, reduceCtorEq] at h <;>
    cases h <;> rfl

section Tensor

variable {A B D H K L : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup D] [Module R D] [AddCommGroup H] [Module R H]
  [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
  {a : GradedContraction R A H} {b : GradedContraction R B K}
  {c : GradedContraction R D L} (f : ChainPairing a b c)

theorem lineFreeTensorChainPairing_mul (d e : ℕ) (x y : Basis →₀ R) (u : A) (v : B) :
    (lineFreeTensorChainPairing R f d e).mul (x ⊗ₜ[R] u) (y ⊗ₜ[R] v) =
      (TensorProduct.congr (lineBasisEquiv R).symm (.refl R D))
        (CechLine.cup d e (lineBasisEquiv R x) (CechLine.evenPart (lineBasisEquiv R y)) ⊗ₜ[R]
            f.mul u v +
          CechLine.cup d e (lineBasisEquiv R x) (CechLine.oddPart (lineBasisEquiv R y)) ⊗ₜ[R]
            f.mul (a.sign u) v) := by
  change (TensorProduct.congr (lineBasisEquiv R).symm (.refl R D))
    (CechLine.tensorChainMul f d e
      (((TensorProduct.congr (lineBasisEquiv R).symm (.refl R A)).symm) (x ⊗ₜ[R] u))
      (((TensorProduct.congr (lineBasisEquiv R).symm (.refl R B)).symm) (y ⊗ₜ[R] v))) = _
  simp only [TensorProduct.congr_symm, TensorProduct.congr_tmul, LinearEquiv.symm_symm,
    LinearEquiv.refl_symm, LinearEquiv.refl_apply, CechLine.tensorChainMul_tmul]

theorem lineFreeTensorChainPairing_mul_basis (d e : ℕ) (x y : Basis) (u : A) (v : B) :
    (lineFreeTensorChainPairing R f d e).mul
      (single x 1 ⊗ₜ[R] u) (single y 1 ⊗ₜ[R] v) =
      (lineCupBasis e x y).elim 0 (fun z =>
        single z 1 ⊗ₜ[R] f.mul ((a.sign ^ lineDegree y) u) v) := by
  rw [lineFreeTensorChainPairing_mul]
  apply (TensorProduct.congr (lineBasisEquiv R) (.refl R D)).injective
  have hz : (((0, 0), 0) : LineC R) = 0 := rfl
  rcases x with x | x | x <;> rcases y with y | y | y <;>
    simp [lineCupBasis, lineDegree, TensorProduct.congr_tmul,
      CechLine.cup, CechLine.evenPart_apply, CechLine.oddPart_apply,
      CechLine.leftRestriction, CechLine.rightRestriction, hz]

end Tensor

theorem finChainPairing_mul_cons {n : ℕ} (d e : Fin (n + 1) → ℕ)
    (x y : Basis) (u v : C R (Fin n)) :
    (finChainPairing R (n + 1) d e).mul
      (consEquiv R _ (single x 1 ⊗ₜ[R] u)) (consEquiv R _ (single y 1 ⊗ₜ[R] v)) =
    consEquiv R _ ((lineCupBasis (e 0) x y).elim 0 (fun z =>
      single z 1 ⊗ₜ[R] (finChainPairing R n (Fin.tail d) (Fin.tail e)).mul
        (((finProduct R n (Fin.tail d)).sign ^ lineDegree y) u) v)) := by
  dsimp only [finChainPairing]
  rw [ChainPairing.congr_mul_apply]
  erw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply,
    lineFreeTensorChainPairing_mul_basis]

def finCupBasis : (n : ℕ) → (Fin n → ℕ) → (Fin n → Basis) → (Fin n → Basis) →
    Option (Fin n → Basis)
  | 0, _, _, _ => some (fun i => Fin.elim0 i)
  | n + 1, e, x, y => do
      let z ← lineCupBasis (e 0) (x 0) (y 0)
      let zs ← finCupBasis n (Fin.tail e) (Fin.tail x) (Fin.tail y)
      pure (Fin.cons z zs)

def finCupCross : (n : ℕ) → (Fin n → Basis) → (Fin n → Basis) → ℕ
  | 0, _, _ => 0
  | n + 1, x, y => cechDegree (Fin.tail x) * lineDegree (y 0) +
      finCupCross n (Fin.tail x) (Fin.tail y)

theorem finProduct_sign_pow_single (n : ℕ) (d : Fin n → ℕ) (b : Fin n → Basis)
    (r : R) (k : ℕ) :
    ((finProduct R n d).sign ^ k) (single b r) =
      (-1 : R) ^ (cechDegree b * k) • single b r := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, finProduct_sign_single,
      smul_smul, ← pow_add, Nat.mul_succ]

theorem finChainPairing_mul_single (n : ℕ) (d e : Fin n → ℕ)
    (x y : Fin n → Basis) (r s : R) :
    (finChainPairing R n d e).mul (single x r) (single y s) =
      (finCupBasis n e x y).elim 0 (fun z =>
        single z ((-1 : R) ^ finCupCross n x y * (r * s))) := by
  induction n with
  | zero => simp [finChainPairing, emptyChainPairing, emptyChainMul, finCupBasis,
      finCupCross, Finsupp.smul_single, mul_comm]
  | succ n ih =>
    conv_lhs =>
      arg 1; rw [← (consEquiv R (fun _ => Basis)).apply_symm_apply (single x r),
        consEquiv_symm_single]
    conv_lhs =>
      arg 2; rw [← (consEquiv R (fun _ => Basis)).apply_symm_apply (single y s),
        consEquiv_symm_single]
    rw [finChainPairing_mul_cons, finProduct_sign_pow_single]
    simp only [map_smul, LinearMap.smul_apply]
    rw [ih]
    cases h₁ : lineCupBasis (e 0) (x 0) (y 0) <;>
      cases h₂ : finCupBasis n (Fin.tail e) (Fin.tail x) (Fin.tail y) <;>
      simp only [finCupBasis, finCupCross, h₁, h₂, Option.elim, Option.bind_eq_bind, Option.bind_none,
        Option.bind_some, Option.pure_def, smul_zero, TensorProduct.tmul_zero, map_zero,
        TensorProduct.tmul_smul, map_smul, consEquiv_single_tmul_single, one_mul,
        Finsupp.smul_single, smul_eq_mul, pow_add, mul_assoc]

end BPFixedPoints.CechProduct
