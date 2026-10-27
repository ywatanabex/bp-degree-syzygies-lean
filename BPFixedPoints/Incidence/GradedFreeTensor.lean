import BPFixedPoints.Incidence.ResolutionGrading
import BPFixedPoints.Incidence.ResolutionHomogeneous
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor product of graded free complexes

Use pairs of basis elements to present the ordinary signed tensor differential
on a free module.
-/

namespace BPFixedPoints.ResolutionTools

open Finsupp
open scoped TensorProduct

universe u
variable {R A : Type u} [CommRing R] (degree : A → ℕ)

noncomputable def gradedParity : Module.End R (A →₀ R) :=
  Finsupp.lsum R fun a => (-1 : R) ^ degree a • Finsupp.lsingle a

@[simp] theorem gradedParity_single (a : A) (r : R) :
    gradedParity degree (single a r) = (-1 : R) ^ degree a • single a r := by
  simp [gradedParity]

theorem gradedParity_apply (x : A →₀ R) (a : A) :
    gradedParity degree x a = (-1 : R) ^ degree a * x a := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, mul_add]
  | single b r => by_cases h : a = b <;> simp [h, Finsupp.single_apply]

theorem gradedParity_degree : HasDegree (fun a => (degree a : ℤ))
    (fun a => (degree a : ℤ)) 0 (gradedParity (R := R) degree) := by
  apply HasDegree.of_single
  intro a r
  rw [gradedParity_single]
  exact Submodule.smul_mem _ _ (single_mem_supported _ _ (by simp))

variable (D : Module.End R (A →₀ R))
  (hdegree : HasDegree (fun a => (degree a : ℤ)) (fun a => (degree a : ℤ)) (-1) D)

include hdegree in
theorem gradedParity_d : gradedParity degree * D = -(D * gradedParity degree) := by
  apply Finsupp.lhom_ext
  intro a r
  apply Finsupp.ext
  intro b
  simp only [Module.End.mul_apply, LinearMap.neg_apply, Finsupp.neg_apply,
    gradedParity_single, map_smul, Finsupp.smul_apply, smul_eq_mul, gradedParity_apply]
  by_cases h : degree b + 1 = degree a
  · rw [← h, pow_succ]
    ring
  · have hb : (degree b : ℤ) ≠ (degree a : ℤ) + -1 := by omega
    rw [(mem_supported' R _).mp (hdegree.apply_single a r) b hb]
    simp

noncomputable def gradedTensorD : Module.End R (A × A →₀ R) :=
  freeTensorMap D 1 + freeTensorMap (gradedParity degree) D

theorem freeTensorMap_comp {B C J K L : Type*}
    (f : (A →₀ R) →ₗ[R] (B →₀ R)) (g : (J →₀ R) →ₗ[R] (K →₀ R))
    (f' : (B →₀ R) →ₗ[R] (C →₀ R)) (g' : (K →₀ R) →ₗ[R] (L →₀ R)) :
    (freeTensorMap f' g').comp (freeTensorMap f g) = freeTensorMap (f'.comp f) (g'.comp g) := by
  apply LinearMap.ext
  intro x
  simp only [freeTensorMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]

include hdegree in
theorem gradedTensorD_sq (hD : D * D = 0) :
    gradedTensorD degree D * gradedTensorD degree D = 0 := by
  have hcancel (f g : Module.End R (A →₀ R)) :
      TensorProduct.map (-f) g + TensorProduct.map f g = 0 := by
    ext x y
    change (-f (single x 1)) ⊗ₜ[R] g (single y 1) + f (single x 1) ⊗ₜ[R] g (single y 1) = 0
    rw [← TensorProduct.add_tmul, neg_add_cancel, TensorProduct.zero_tmul]
  let e := finsuppTensorFinsupp' R A A
  have h : (TensorProduct.map D 1 + TensorProduct.map (gradedParity degree) D) *
      (TensorProduct.map D 1 + TensorProduct.map (gradedParity degree) D) = 0 := by
    simp only [add_mul, mul_add, ← TensorProduct.map_mul, hD,
      one_mul, mul_one, gradedParity_d degree D hdegree,
      TensorProduct.map_zero_left, TensorProduct.map_zero_right, add_zero, zero_add]
    exact hcancel _ _
  apply LinearMap.ext
  intro x
  have hx := congrArg e (LinearMap.congr_fun h (e.symm x))
  simpa only [gradedTensorD, freeTensorMap, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, ← map_add, LinearEquiv.symm_apply_apply,
    LinearMap.zero_apply, map_zero] using hx

include hdegree in
theorem gradedTensorD_degree : HasDegree (fun a : A × A => ((degree a.1 + degree a.2 : ℕ) : ℤ))
    (fun a : A × A => ((degree a.1 + degree a.2 : ℕ) : ℤ)) (-1) (gradedTensorD degree D) := by
  have h₁ := hdegree.freeTensorMap (HasDegree.id (R := R) (M := R) (fun a => (degree a : ℤ)))
  have h₂ := (gradedParity_degree (R := R) degree).freeTensorMap hdegree
  simpa only [Nat.cast_add, add_zero, zero_add, gradedTensorD, Module.End.one_eq_id] using h₁.add h₂

include hdegree in
theorem gradedTensorD_graded (n : ℕ) (x : A × A →₀ R)
    (hx : x ∈ gradedPiece R (fun a => degree a.1 + degree a.2) (n + 1)) :
    gradedTensorD degree D x ∈ gradedPiece R (fun a => degree a.1 + degree a.2) n := by
  have hx' : x ∈ supported R R {a | ((degree a.1 + degree a.2 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ)} := by
    simpa only [gradedPiece, Int.natCast_inj] using hx
  have h := gradedTensorD_degree degree D hdegree _ x hx'
  rw [show ((n + 1 : ℕ) : ℤ) + -1 = (n : ℤ) from by omega] at h
  simpa only [Int.natCast_inj, gradedPiece] using h

theorem gradedTensorD_tmul (x y : A →₀ R) :
    gradedTensorD degree D (finsuppTensorFinsupp' R A A (x ⊗ₜ[R] y)) =
      finsuppTensorFinsupp' R A A
        (D x ⊗ₜ[R] y + gradedParity degree x ⊗ₜ[R] D y) := by
  simp only [gradedTensorD, freeTensorMap, LinearMap.add_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, TensorProduct.map_tmul,
    Module.End.one_apply, map_add]

theorem gradedTensorD_minimal (I : Ideal R) (hD : ∀ x, D x ∈ I • (⊤ : Submodule R (A →₀ R)))
    (x : A × A →₀ R) : gradedTensorD degree D x ∈ I • (⊤ : Submodule R (A × A →₀ R)) := by
  induction x using Finsupp.induction_linear with
  | zero => simpa using (Submodule.zero_mem (I • (⊤ : Submodule R (A × A →₀ R))))
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | single ab r =>
    have he : single ab r = finsuppTensorFinsupp' R A A
        (single ab.1 1 ⊗ₜ[R] single ab.2 r) := by simp
    rw [he, gradedTensorD_tmul]
    apply map_mem_ideal_smul_top I (finsuppTensorFinsupp' R A A).toLinearMap
    apply Submodule.add_mem
    · exact map_mem_ideal_smul_top I ((TensorProduct.mk R (A →₀ R) (A →₀ R)).flip
        (single ab.2 r)) (hD (single ab.1 1))
    · exact map_mem_ideal_smul_top I ((TensorProduct.mk R (A →₀ R) (A →₀ R))
        (gradedParity degree (single ab.1 1))) (hD (single ab.2 r))

end BPFixedPoints.ResolutionTools
