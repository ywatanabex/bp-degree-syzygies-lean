import BPFixedPoints.Incidence.GradedMixedTensor
import BPFixedPoints.Incidence.GradedFreePairingLaws

/-! # The signed opposite product respects the same differential -/
namespace BPFixedPoints.ResolutionTools
open Finsupp
open scoped TensorProduct
universe u
variable {R A : Type u} [CommRing R] {degree : A → ℕ} {D : Module.End R (A →₀ R)}
namespace GradedFreePairing
variable (μ : GradedFreePairing degree D)

noncomputable def oppositeMul : (A →₀ R) →ₗ[R] (A →₀ R) →ₗ[R] (A →₀ R) :=
  Finsupp.lsum R fun a => LinearMap.toSpanSingleton R _
    ((μ.rightMul (single a 1)).comp (gradedParity degree ^ degree a))

theorem oppositeMul_single (a : A) (r : R) (y : A →₀ R) :
    μ.oppositeMul (single a r) y = μ.mul ((gradedParity degree ^ degree a) y) (single a r) := by
  simp only [oppositeMul, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, rightMul_apply]
  rw [show single a r = r • single a (1 : R) from by simp, map_smul]

theorem oppositeMul_homogeneous_left (p : ℕ) {x : A →₀ R}
    (hx : x ∈ gradedPiece R degree p) (y : A →₀ R) :
    μ.oppositeMul x y = μ.mul ((gradedParity degree ^ p) y) x := by
  rw [← x.sum_single, map_finsuppSum]
  simp only [Finsupp.sum, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [oppositeMul_single, (mem_supported R x).mp hx ha]

theorem oppositeMul_homogeneous (p q : ℕ) {x y : A →₀ R}
    (hx : x ∈ gradedPiece R degree p) (hy : y ∈ gradedPiece R degree q) :
    μ.oppositeMul x y = (-1 : R) ^ (p * q) • μ.mul y x := by
  rw [μ.oppositeMul_homogeneous_left p hx, gradedParity_pow_homogeneous degree p q hy,
    LinearMap.map_smul₂]

theorem oppositeMul_zero (x y : A →₀ R) (hx : x ∈ gradedPiece R degree 0) :
    μ.oppositeMul x y = μ.mul y x := by
  rw [μ.oppositeMul_homogeneous_left 0 hx]
  rfl

theorem oppositeMul_baseChange {k : Type u} [CommRing k] [Algebra R k]
    (p q : ℕ) {x y : A →₀ R}
    (hx : x ∈ gradedPiece R degree p) (hy : y ∈ gradedPiece R degree q) :
    (1 : k) ⊗ₜ[R] μ.oppositeMul x y =
      (-1 : k) ^ (p * q) • ((1 : k) ⊗ₜ[R] μ.mul y x) := by
  rw [μ.oppositeMul_homogeneous p q hx hy, ← TensorProduct.smul_tmul,
    Algebra.smul_def, map_pow, map_neg, map_one, mul_one, TensorProduct.smul_tmul']
  simp only [smul_eq_mul, mul_one]

theorem oppositeMul_degree (p q : ℕ) {x y : A →₀ R}
    (hx : x ∈ gradedPiece R degree p) (hy : y ∈ gradedPiece R degree q) :
    μ.oppositeMul x y ∈ gradedPiece R degree (p + q) := by
  rw [μ.oppositeMul_homogeneous p q hx hy]
  apply Submodule.smul_mem
  simpa only [Nat.add_comm q p] using μ.homogeneous q p hy hx

variable (hd : HasDegree (fun a => (degree a : ℤ)) (fun a => (degree a : ℤ)) (-1) D)

include hd in
theorem oppositeMul_leibniz (x y : A →₀ R) :
    D (μ.oppositeMul x y) = μ.oppositeMul (D x) y +
      μ.oppositeMul (gradedParity degree x) (D y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']; abel
  | single a r =>
    rw [oppositeMul_single, μ.leibniz, d_gradedParity_pow degree D hd,
      LinearMap.map_smul₂, gradedParity_single, LinearMap.map_smul₂,
      oppositeMul_single]
    have hxa : single a r ∈ gradedPiece R degree (degree a) := single_mem_supported _ _ rfl
    cases h : degree a with
    | zero =>
      have hx0 : single a r ∈ gradedPiece R degree 0 := h ▸ hxa
      rw [differential_zero_degree degree D hd hx0]
      simp
    | succ n =>
      have hDxa : D (single a r) ∈ gradedPiece R degree n :=
        hd.nat_differential n _ (h ▸ hxa)
      rw [μ.oppositeMul_homogeneous_left n hDxa]
      have hp : gradedParity degree ((gradedParity degree ^ (n + 1)) y) =
          (gradedParity degree ^ n) y := by
        rw [← Module.End.mul_apply, ← pow_succ', gradedParity_pow_two_add]
      rw [hp]
      exact add_comm _ _

noncomputable def opposite : GradedFreePairing degree D where
  mul := μ.oppositeMul
  homogeneous := μ.oppositeMul_degree
  leibniz := μ.oppositeMul_leibniz hd

end GradedFreePairing
end BPFixedPoints.ResolutionTools
