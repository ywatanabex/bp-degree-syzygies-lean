import BPFixedPoints.Incidence.CoefficientGrading
import BPFixedPoints.Incidence.HomogeneousQuotient
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Homogeneous polynomial evaluation and weighted free presentations -/

namespace BPFixedPoints.ResolutionTools

open MvPolynomial Finsupp
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k A σ : Type*} [Field k] [CommRing A] [Algebra k A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]

/-- Sending the polynomial variables to degree one preserves homogeneous degree. -/
theorem polynomial_map_homogeneous (f : MvPolynomial σ k →ₐ[k] A)
    (hf : ∀ i, f (X i) ∈ 𝒜 1) {p : MvPolynomial σ k} {q : ℕ}
    (hp : p.IsHomogeneous q) : f p ∈ 𝒜 q := by
  classical
  have hf' : f = aeval (fun i => f (X i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro d hd
  have hdq : d.degree = q := by
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hd) (hp.coeff_eq_zero hn)
  rw [hf', aeval_monomial, ← Algebra.smul_def]
  apply Submodule.smul_mem
  have hprod := SetLike.prod_pow_mem_graded 𝒜 (fun _ : σ => (1 : ℕ))
    (fun i => f (X i)) d (F := d.support) (fun i _ => hf i)
  have hdeg : (∑ i ∈ d.support, d i) = q := hdq
  simpa only [Finsupp.prod, smul_eq_mul, mul_one, hdeg] using hprod

variable [Algebra (MvPolynomial σ k) A] [IsScalarTower k (MvPolynomial σ k) A]
  {I : Type*} (w : I → ℕ) (v : I → A)

/-- The actual polynomial-linear presentation preserves its assigned generator weights. -/
theorem linearCombination_weighted_degree
    (hx : ∀ i : σ, algebraMap (MvPolynomial σ k) A (X i) ∈ 𝒜 1)
    (hv : ∀ i, v i ∈ 𝒜 (w i)) {q : ℕ} {z : I →₀ MvPolynomial σ k}
    (hz : z ∈ weightedFreePiece w (q : ℤ)) :
    Finsupp.linearCombination (MvPolynomial σ k) v z ∈ 𝒜 q := by
  classical
  rw [Finsupp.linearCombination_apply]
  apply Submodule.sum_mem
  intro i _
  change z i • v i ∈ 𝒜 q
  by_cases hi : w i ≤ q
  · have hh : (z i).IsHomogeneous (q - w i) := by
      have h := hz i
      have he : (q : ℤ) - w i = ((q - w i : ℕ) : ℤ) := by omega
      rwa [he, homogeneousCoeffPiece_nat] at h
    have hm := SetLike.GradedMul.mul_mem
      (polynomial_map_homogeneous 𝒜 (IsScalarTower.toAlgHom k (MvPolynomial σ k) A) hx hh) (hv i)
    change algebraMap (MvPolynomial σ k) A (z i) * v i ∈ 𝒜 (q - w i + w i) at hm
    simpa only [Nat.sub_add_cancel hi, Algebra.smul_def] using hm
  · have hzi : z i = 0 := by
      have h := hz i
      rw [homogeneousCoeffPiece_negative (by omega)] at h
      exact h
    rw [hzi, zero_smul]
    exact (𝒜 q).zero_mem

/-- Multiplying a weighted homogeneous vector by a variable raises its degree by one. -/
theorem weightedFreePiece_X_smul {q : ℕ} {z : I →₀ MvPolynomial σ k}
    (hz : z ∈ weightedFreePiece w (q : ℤ)) (j : σ) :
    (X j : MvPolynomial σ k) • z ∈ weightedFreePiece w ((q + 1 : ℕ) : ℤ) := by
  intro i
  have h := homogeneousCoeffPiece_mul (homogeneousCoeffPiece_X (k := k) j) (hz i)
  change X j * z i ∈ homogeneousCoeffPiece _
  convert h using 1 <;> congr 1 <;> omega

end BPFixedPoints.ResolutionTools
