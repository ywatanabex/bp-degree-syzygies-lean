import BPFixedPoints.Incidence.CechChainPairing

/-!
# Signed tensor product of one-vertex Alexander–Whitney products

Project arbitrary chains to degrees zero and one; insert the parity operator
when moving the right input's degree-one component past the remaining complex
of the left input. No division by two is needed.
-/

namespace BPFixedPoints

open scoped TensorProduct
open CechProduct GradedContraction

namespace CechLine

variable {R : Type*} [CommRing R]

noncomputable def evenPart : Module.End R (LineC R) := LinearMap.id.prodMap 0
noncomputable def oddPart : Module.End R (LineC R) := (0 : Module.End R (C0 R)).prodMap LinearMap.id

@[simp] theorem evenPart_apply (x : LineC R) : evenPart x = (x.1, 0) := rfl
@[simp] theorem oddPart_apply (x : LineC R) : oddPart x = (0, x.2) := rfl

theorem cup_sign (d e : ℕ) (x y : LineC R) :
    lineSign R (cup d e x y) = cup d e (lineSign R x) (lineSign R y) := by
  simp [cup, add_comm]

theorem cup_neg_right (d e : ℕ) (x y : LineC R) : cup d e x (-y) = -cup d e x y :=
  map_neg (cupLinear d e x) y

noncomputable def chainPairing (d e : ℕ) : ChainPairing (line R d) (line R e) (line R (d + e)) where
  mul := cupLinear d e
  leibniz := cup_leibniz d e
  sign_mul := cup_sign d e

theorem d_evenPart (d : ℕ) (x : LineC R) : lineD R d (evenPart x) = lineD R d x := rfl
@[simp] theorem d_oddPart (d : ℕ) (x : LineC R) : lineD R d (oddPart x) = 0 := by simp
@[simp] theorem evenPart_d (d : ℕ) (x : LineC R) : evenPart (lineD R d x) = 0 := rfl
@[simp] theorem oddPart_d (d : ℕ) (x : LineC R) : oddPart (lineD R d x) = lineD R d x := rfl
@[simp] theorem evenPart_sign (x : LineC R) : evenPart (lineSign R x) = evenPart x := rfl
@[simp] theorem oddPart_sign (x : LineC R) : oddPart (lineSign R x) = -oddPart x := by simp
@[simp] theorem sign_evenPart (x : LineC R) : lineSign R (evenPart x) = evenPart x := by simp
@[simp] theorem sign_oddPart (x : LineC R) : lineSign R (oddPart x) = -oddPart x := by simp

section Tensor

variable {A B C H K L : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup H] [Module R H]
  [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
  {a : GradedContraction R A H} {b : GradedContraction R B K}
  {c : GradedContraction R C L} (f : ChainPairing a b c)

noncomputable def tensorChainMul (d e : ℕ) :
    (LineC R ⊗[R] A) →ₗ[R] (LineC R ⊗[R] B) →ₗ[R] (LineC R ⊗[R] C) :=
  CupTools.tensorBilinear ((cupLinear d e).compl₂ evenPart) f.mul +
    CupTools.tensorBilinear ((cupLinear d e).compl₂ oddPart) (f.mul.comp a.sign)

theorem tensorChainMul_tmul (d e : ℕ) (x y : LineC R) (u : A) (v : B) :
    tensorChainMul f d e (x ⊗ₜ[R] u) (y ⊗ₜ[R] v) =
      cup d e x (evenPart y) ⊗ₜ[R] f.mul u v +
        cup d e x (oddPart y) ⊗ₜ[R] f.mul (a.sign u) v := rfl

theorem tensorChainMul_leibniz_tmul (d e : ℕ) (x y : LineC R) (u : A) (v : B) :
    ((line R (d + e)).tensor c).d (tensorChainMul f d e (x ⊗ₜ[R] u) (y ⊗ₜ[R] v)) =
      tensorChainMul f d e (((line R d).tensor a).d (x ⊗ₜ[R] u)) (y ⊗ₜ[R] v) +
      tensorChainMul f d e (((line R d).tensor a).sign (x ⊗ₜ[R] u))
        (((line R e).tensor b).d (y ⊗ₜ[R] v)) := by
  simp only [GradedContraction.tensor, tensorD, LinearMap.add_apply,
    TensorProduct.map_tmul, Module.End.one_apply, line, map_add,
    tensorChainMul_tmul, cup_leibniz, cup_sign, d_evenPart, d_oddPart,
    evenPart_d, oddPart_d, evenPart_sign, oddPart_sign, sign_evenPart, sign_oddPart,
    cup_zero_right, cup_neg_right, LinearMap.neg_apply,
    f.leibniz, a.sign_sign_apply, a.d_sign_apply, map_neg,
    TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.neg_tmul,
    TensorProduct.tmul_neg, TensorProduct.zero_tmul, zero_add, add_zero]
  abel

noncomputable def tensorChainPairing (d e : ℕ) :
    ChainPairing ((line R d).tensor a) ((line R e).tensor b) ((line R (d + e)).tensor c) where
  mul := tensorChainMul f d e
  leibniz x y := by
    have heq : (tensorChainMul f d e).compr₂ ((line R (d + e)).tensor c).d =
        (tensorChainMul f d e).comp ((line R d).tensor a).d +
        (tensorChainMul f d e).compl₁₂ ((line R d).tensor a).sign ((line R e).tensor b).d := by
      apply TensorProduct.ext'
      intro x u
      apply TensorProduct.ext'
      intro y v
      exact tensorChainMul_leibniz_tmul f d e x y u v
    exact LinearMap.congr_fun (LinearMap.congr_fun heq x) y
  sign_mul x y := by
    have heq : (tensorChainMul f d e).compr₂ ((line R (d + e)).tensor c).sign =
        (tensorChainMul f d e).compl₁₂ ((line R d).tensor a).sign ((line R e).tensor b).sign := by
      apply TensorProduct.ext'
      intro x u
      apply TensorProduct.ext'
      intro y v
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
        GradedContraction.tensor, TensorProduct.map_tmul, line,
        tensorChainMul_tmul, map_add, cup_sign, sign_evenPart, sign_oddPart,
        evenPart_sign, oddPart_sign, f.sign_mul, a.sign_sign_apply]
    exact LinearMap.congr_fun (LinearMap.congr_fun heq x) y

end Tensor
end CechLine
end BPFixedPoints
