import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Finite-dimensional quotients from nilpotent coefficient variables -/

namespace BPFixedPoints.ResolutionTools

open MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k σ A : Type*} [Field k] [Finite σ] [CommRing A] [Algebra k A]
  [Algebra (MvPolynomial σ k) A] [IsScalarTower k (MvPolynomial σ k) A]
  [Module.Finite (MvPolynomial σ k) A]

/-- A finite algebra over a polynomial ring is finite over the field if all coefficient
variables become nilpotent. The algebra itself need not be reduced. -/
theorem finite_of_polynomial_variables_nilpotent (N : ℕ) (hN : 0 < N)
    (h : ∀ i : σ, (algebraMap (MvPolynomial σ k) A (X i)) ^ N = 0) : Module.Finite k A := by
  let φ : MvPolynomial σ k →ₐ[k] A := IsScalarTower.toAlgHom k (MvPolynomial σ k) A
  have he : aeval (fun i => φ (X i)) = φ := by ext i; simp
  have hr : φ.range = Algebra.adjoin k (Set.range (fun i => φ (X i))) := by
    rw [← he, aeval_range]
    simp only [aeval_X]
  have hf : Module.Finite k φ.range := by
    rw [hr]
    apply Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range _)
    rintro _ ⟨i, rfl⟩
    apply IsIntegral.of_pow hN
    change IsIntegral k ((algebraMap (MvPolynomial σ k) A (X i)) ^ N)
    rw [h i]
    exact isIntegral_zero
  letI : Algebra (MvPolynomial σ k) φ.range := φ.rangeRestrict.toRingHom.toAlgebra
  letI : IsScalarTower (MvPolynomial σ k) φ.range A :=
    IsScalarTower.of_algebraMap_eq (fun r => rfl)
  letI : Module.Finite φ.range A := Module.Finite.of_restrictScalars_finite (MvPolynomial σ k) φ.range A
  exact Module.Finite.trans φ.range A

end BPFixedPoints.ResolutionTools
