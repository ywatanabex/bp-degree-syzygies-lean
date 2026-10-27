import BPFixedPoints.Incidence.CechLine
import BPFixedPoints.Incidence.Perturbation
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Tensor product of Čech contractions

Equip a strong contraction with the grading-parity involution. Tensor two by
d=d₁⊗1+ε₁⊗d₂ and h=h₁⊗1+(i₁p₁ε₁)⊗h₂.
-/

namespace BPFixedPoints

open scoped TensorProduct

variable (R C H : Type*) [CommRing R] [AddCommGroup C] [Module R C]
  [AddCommGroup H] [Module R H]

/-- Parity-preserving strong contraction to cohomology with zero differential. -/
structure GradedContraction extends IncidencePerturbation.Contraction R C H where
  sign : Module.End R C
  signH : Module.End R H
  sign_sq : sign * sign = 1
  signH_sq : signH * signH = 1
  sign_d : sign * d = -(d * sign)
  sign_h : sign * h = -(h * sign)
  sign_i : sign.comp i = i.comp signH
  p_sign : p.comp sign = signH.comp p

namespace GradedContraction

variable {R C H}
variable (c : GradedContraction R C H)

def projection : Module.End R C := c.i.comp c.p

theorem d_projection : c.d * c.projection = 0 := by
  change c.d.comp (c.i.comp c.p) = 0
  rw [← LinearMap.comp_assoc, c.d_i, LinearMap.zero_comp]

theorem projection_d : c.projection * c.d = 0 := by
  change (c.i.comp c.p).comp c.d = 0
  rw [LinearMap.comp_assoc, c.p_d, LinearMap.comp_zero]

theorem h_projection : c.h * c.projection = 0 := by
  change c.h.comp (c.i.comp c.p) = 0
  rw [← LinearMap.comp_assoc, c.h_i, LinearMap.zero_comp]

theorem projection_h : c.projection * c.h = 0 := by
  change (c.i.comp c.p).comp c.h = 0
  rw [LinearMap.comp_assoc, c.p_h, LinearMap.comp_zero]

theorem sign_projection : c.sign * c.projection = c.projection * c.sign := by
  change c.sign.comp (c.i.comp c.p) = (c.i.comp c.p).comp c.sign
  rw [← LinearMap.comp_assoc, c.sign_i, LinearMap.comp_assoc,
    ← c.p_sign, ← LinearMap.comp_assoc]

theorem projection_sq : c.projection * c.projection = c.projection := by
  change (c.i.comp c.p).comp (c.i.comp c.p) = c.i.comp c.p
  rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc c.p c.i c.p,
    c.p_i, LinearMap.id_comp]

theorem dh_eq : c.d * c.h = 1 - c.h * c.d - c.projection := by
  have hc := c.homotopy
  change c.d * c.h + c.h * c.d + c.projection = 1 at hc
  linear_combination (norm := noncomm_ring) hc

theorem projection_sign_d : c.projection * c.sign * c.d = 0 := by
  rw [mul_assoc, c.sign_d, mul_neg, ← mul_assoc, c.projection_d, zero_mul, neg_zero]

theorem projection_sign_h : c.projection * c.sign * c.h = 0 := by
  rw [mul_assoc, c.sign_h, mul_neg, ← mul_assoc, c.projection_h, zero_mul, neg_zero]

theorem sign_projection_sign : c.sign * (c.projection * c.sign) = c.projection := by
  rw [← mul_assoc, c.sign_projection, mul_assoc, c.sign_sq, mul_one]

theorem projection_sign_sq : (c.projection * c.sign) * c.sign = c.projection := by
  rw [mul_assoc, c.sign_sq, mul_one]

section Tensor

variable {D K : Type*} [AddCommGroup D] [Module R D] [AddCommGroup K] [Module R K]
variable (e : GradedContraction R D K)

private theorem map_neg_left {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    (f : A →ₗ[R] A') (g : B →ₗ[R] B') :
    TensorProduct.map (-f) g = -TensorProduct.map f g := by
  ext x y
  simp [TensorProduct.neg_tmul]

private theorem map_neg_right {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    (f : A →ₗ[R] A') (g : B →ₗ[R] B') :
    TensorProduct.map f (-g) = -TensorProduct.map f g := by
  ext x y
  simp [TensorProduct.tmul_neg]

private theorem map_sub_left {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    (f f' : A →ₗ[R] A') (g : B →ₗ[R] B') :
    TensorProduct.map (f - f') g = TensorProduct.map f g - TensorProduct.map f' g := by
  rw [sub_eq_add_neg, TensorProduct.map_add_left, map_neg_left, sub_eq_add_neg]

private theorem map_sub_right {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    (f : A →ₗ[R] A') (g g' : B →ₗ[R] B') :
    TensorProduct.map f (g - g') = TensorProduct.map f g - TensorProduct.map f g' := by
  rw [sub_eq_add_neg, TensorProduct.map_add_right, map_neg_right, sub_eq_add_neg]

noncomputable def tensorD : Module.End R (C ⊗[R] D) :=
  TensorProduct.map c.d 1 + TensorProduct.map c.sign e.d

noncomputable def tensorH : Module.End R (C ⊗[R] D) :=
  TensorProduct.map c.h 1 + TensorProduct.map (c.projection * c.sign) e.h

noncomputable def tensorI : H ⊗[R] K →ₗ[R] C ⊗[R] D := TensorProduct.map c.i e.i
noncomputable def tensorP : C ⊗[R] D →ₗ[R] H ⊗[R] K := TensorProduct.map c.p e.p

theorem tensorD_sq : c.tensorD e * c.tensorD e = 0 := by
  simp only [tensorD, add_mul, mul_add, ← TensorProduct.map_mul,
    c.d_sq, e.d_sq, one_mul, mul_one, c.sign_d,
    TensorProduct.map_zero_left, TensorProduct.map_zero_right, map_neg_left]
  abel

theorem tensorH_sq : c.tensorH e * c.tensorH e = 0 := by
  have hh : c.h * (c.projection * c.sign) = 0 := by
    rw [← mul_assoc, c.h_projection, zero_mul]
  simp only [tensorH, add_mul, mul_add, ← TensorProduct.map_mul,
    c.h_sq, e.h_sq, one_mul, mul_one, hh, c.projection_sign_h,
    TensorProduct.map_zero_left, TensorProduct.map_zero_right, add_zero]

theorem tensorD_i : (c.tensorD e).comp (c.tensorI e) = 0 := by
  simp only [tensorD, tensorI, LinearMap.add_comp, ← TensorProduct.map_comp,
    c.d_i, e.d_i,
    TensorProduct.map_zero_left, TensorProduct.map_zero_right, add_zero]

theorem tensorP_d : (c.tensorP e).comp (c.tensorD e) = 0 := by
  simp only [tensorD, tensorP, LinearMap.comp_add, ← TensorProduct.map_comp,
    c.p_d, e.p_d,
    TensorProduct.map_zero_left, TensorProduct.map_zero_right, add_zero]

theorem tensorP_i : (c.tensorP e).comp (c.tensorI e) = LinearMap.id := by
  rw [tensorP, tensorI, ← TensorProduct.map_comp, c.p_i, e.p_i, TensorProduct.map_id]

theorem tensorH_i : (c.tensorH e).comp (c.tensorI e) = 0 := by
  simp only [tensorH, tensorI, LinearMap.add_comp, ← TensorProduct.map_comp,
    c.h_i, e.h_i,
    TensorProduct.map_zero_left, TensorProduct.map_zero_right, add_zero]

theorem tensorP_h : (c.tensorP e).comp (c.tensorH e) = 0 := by
  simp only [tensorH, tensorP, LinearMap.comp_add, ← TensorProduct.map_comp,
    c.p_h, e.p_h,
    TensorProduct.map_zero_left, TensorProduct.map_zero_right, add_zero]

theorem tensor_homotopy :
    c.tensorD e * c.tensorH e + c.tensorH e * c.tensorD e +
      (c.tensorI e).comp (c.tensorP e) = 1 := by
  have hd : c.d * (c.projection * c.sign) = 0 := by
    rw [← mul_assoc, c.d_projection, zero_mul]
  simp only [tensorD, tensorH, tensorI, tensorP, add_mul, mul_add,
    ← TensorProduct.map_mul, ← TensorProduct.map_comp,
    one_mul, mul_one, hd, c.projection_sign_d, c.sign_projection_sign,
    c.projection_sign_sq, c.sign_h, map_neg_left,
    TensorProduct.map_zero_left, TensorProduct.map_zero_right,
    c.dh_eq, e.dh_eq, map_sub_left, map_sub_right,
    TensorProduct.map_one]
  change _ + TensorProduct.map c.projection e.projection = 1
  abel

/-- Tensor product of two strong contractions with parity. -/
noncomputable def tensor : GradedContraction R (C ⊗[R] D) (H ⊗[R] K) where
  d := c.tensorD e
  h := c.tensorH e
  i := c.tensorI e
  p := c.tensorP e
  d_sq := c.tensorD_sq e
  d_i := c.tensorD_i e
  p_d := c.tensorP_d e
  p_i := c.tensorP_i e
  homotopy := c.tensor_homotopy e
  h_sq := c.tensorH_sq e
  h_i := c.tensorH_i e
  p_h := c.tensorP_h e
  sign := TensorProduct.map c.sign e.sign
  signH := TensorProduct.map c.signH e.signH
  sign_sq := by rw [← TensorProduct.map_mul, c.sign_sq, e.sign_sq, TensorProduct.map_one]
  signH_sq := by rw [← TensorProduct.map_mul, c.signH_sq, e.signH_sq, TensorProduct.map_one]
  sign_d := by
    simp only [tensorD, mul_add, add_mul, ← TensorProduct.map_mul,
      one_mul, mul_one, c.sign_d, e.sign_d, map_neg_left, map_neg_right]
    abel
  sign_h := by
    simp only [tensorH, mul_add, add_mul, ← TensorProduct.map_mul,
      one_mul, mul_one, c.sign_h, e.sign_h, c.sign_projection_sign,
      c.projection_sign_sq, map_neg_left, map_neg_right]
    abel
  sign_i := by
    rw [tensorI, ← TensorProduct.map_comp, ← TensorProduct.map_comp, c.sign_i, e.sign_i]
  p_sign := by
    rw [tensorP, ← TensorProduct.map_comp, ← TensorProduct.map_comp, c.p_sign, e.p_sign]

end Tensor

section Equivalence

variable {C' H' : Type*} [AddCommGroup C'] [Module R C']
  [AddCommGroup H'] [Module R H']

private def transportMap {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    (a : A ≃ₗ[R] A') (b : B ≃ₗ[R] B') (f : A →ₗ[R] B) : A' →ₗ[R] B' :=
  b.toLinearMap.comp (f.comp a.symm.toLinearMap)

private theorem transportMap_apply {A B A' B' : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    (a : A ≃ₗ[R] A') (b : B ≃ₗ[R] B') (f : A →ₗ[R] B) (x : A') :
    transportMap a b f x = b (f (a.symm x)) := rfl

/-- Transfer a strong contraction along a linear coordinate equivalence. -/
noncomputable def congr (a : C ≃ₗ[R] C') (b : H ≃ₗ[R] H') :
    GradedContraction R C' H' where
  d := transportMap a a c.d
  h := transportMap a a c.h
  i := transportMap b a c.i
  p := transportMap a b c.p
  sign := transportMap a a c.sign
  signH := transportMap b b c.signH
  d_sq := by
    ext x
    simpa [transportMap, Module.End.mul_eq_comp] using
      congrArg a (LinearMap.congr_fun c.d_sq (a.symm x))
  d_i := by
    ext x
    simpa [transportMap] using congrArg a (LinearMap.congr_fun c.d_i (b.symm x))
  p_d := by
    ext x
    simpa [transportMap] using congrArg b (LinearMap.congr_fun c.p_d (a.symm x))
  p_i := by
    ext x
    simpa [transportMap] using congrArg b (LinearMap.congr_fun c.p_i (b.symm x))
  homotopy := by
    ext x
    simpa [transportMap, Module.End.mul_eq_comp] using
      congrArg a (LinearMap.congr_fun c.homotopy (a.symm x))
  h_sq := by
    ext x
    simpa [transportMap, Module.End.mul_eq_comp] using
      congrArg a (LinearMap.congr_fun c.h_sq (a.symm x))
  h_i := by
    ext x
    simpa [transportMap] using congrArg a (LinearMap.congr_fun c.h_i (b.symm x))
  p_h := by
    ext x
    simpa [transportMap] using congrArg b (LinearMap.congr_fun c.p_h (a.symm x))
  sign_sq := by
    ext x
    simpa [transportMap, Module.End.mul_eq_comp] using
      congrArg a (LinearMap.congr_fun c.sign_sq (a.symm x))
  signH_sq := by
    ext x
    simpa [transportMap, Module.End.mul_eq_comp] using
      congrArg b (LinearMap.congr_fun c.signH_sq (b.symm x))
  sign_d := by
    ext x
    simpa [transportMap, Module.End.mul_eq_comp] using
      congrArg a (LinearMap.congr_fun c.sign_d (a.symm x))
  sign_h := by
    ext x
    simpa [transportMap, Module.End.mul_eq_comp] using
      congrArg a (LinearMap.congr_fun c.sign_h (a.symm x))
  sign_i := by
    ext x
    simpa [transportMap] using congrArg a (LinearMap.congr_fun c.sign_i (b.symm x))
  p_sign := by
    ext x
    simpa [transportMap] using congrArg b (LinearMap.congr_fun c.p_sign (a.symm x))

@[simp] theorem congr_d_apply (a : C ≃ₗ[R] C') (b : H ≃ₗ[R] H') (x : C') :
    (c.congr a b).d x = a (c.d (a.symm x)) := rfl

@[simp] theorem congr_h_apply (a : C ≃ₗ[R] C') (b : H ≃ₗ[R] H') (x : C') :
    (c.congr a b).h x = a (c.h (a.symm x)) := rfl

@[simp] theorem congr_i_apply (a : C ≃ₗ[R] C') (b : H ≃ₗ[R] H') (x : H') :
    (c.congr a b).i x = a (c.i (b.symm x)) := rfl

@[simp] theorem congr_p_apply (a : C ≃ₗ[R] C') (b : H ≃ₗ[R] H') (x : C') :
    (c.congr a b).p x = b (c.p (a.symm x)) := rfl

@[simp] theorem congr_sign_apply (a : C ≃ₗ[R] C') (b : H ≃ₗ[R] H') (x : C') :
    (c.congr a b).sign x = a (c.sign (a.symm x)) := rfl

@[simp] theorem congr_signH_apply (a : C ≃ₗ[R] C') (b : H ≃ₗ[R] H') (x : H') :
    (c.congr a b).signH x = b (c.signH (b.symm x)) := rfl

end Equivalence

end GradedContraction

end BPFixedPoints
