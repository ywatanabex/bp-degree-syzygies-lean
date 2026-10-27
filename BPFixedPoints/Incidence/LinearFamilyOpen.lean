import BPFixedPoints.Incidence.PolynomialRankOpen
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Polynomial certificates for finite-dimensional linear families -/

namespace BPFixedPoints.ResolutionTools

open MvPolynomial Matrix
set_option backward.isDefEq.respectTransparency false

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N]

theorem matrix_mulVec_surjective_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (bM : Module.Basis ι k M) (bN : Module.Basis κ k N)
    (f : M →ₗ[k] N) :
    Function.Surjective (LinearMap.toMatrix bM bN f).mulVec ↔ Function.Surjective f := by
  have he (x : M) : (LinearMap.toMatrix bM bN f) *ᵥ bM.equivFun x = bN.equivFun (f x) :=
    f.toMatrix_mulVec_repr bM bN x
  constructor
  · intro hs y
    obtain ⟨x, hx⟩ := hs (bN.equivFun y)
    refine ⟨bM.equivFun.symm x, bN.equivFun.injective ?_⟩
    rw [← he, bM.equivFun.apply_symm_apply]
    exact hx
  · intro hs y
    obtain ⟨x, hx⟩ := hs (bN.equivFun.symm y)
    exact ⟨bM.equivFun x, by rw [he, hx, bN.equivFun.apply_symm_apply]⟩

variable [Module.Finite k M] [Module.Finite k N] {σ : Type*} [Fintype σ]

/-- Surjectivity of a linear family persists on a principal open set containing the witness. -/
theorem exists_linear_family_surjectivity_certificate (f : σ → M →ₗ[k] N)
    (a : σ → k) (ha : Function.Surjective (∑ i, a i • f i : M →ₗ[k] N)) :
    ∃ P : MvPolynomial σ k, eval a P ≠ 0 ∧
      ∀ b : σ → k, eval b P ≠ 0 → Function.Surjective (∑ i, b i • f i : M →ₗ[k] N) := by
  classical
  let bM := Module.Free.chooseBasis k M
  let bN := Module.Free.chooseBasis k N
  let T : Matrix (Module.Free.ChooseBasisIndex k N) (Module.Free.ChooseBasisIndex k M)
      (MvPolynomial σ k) := fun i j => ∑ c, X c * C (LinearMap.toMatrix bM bN (f c) i j)
  have he (b : σ → k) : T.map (eval b) = LinearMap.toMatrix bM bN (∑ c, b c • f c) := by
    ext i j
    simp [T, LinearMap.toMatrix_apply, LinearMap.sum_apply, Finsupp.sum_apply]
  obtain ⟨P, hP, hp⟩ := exists_polynomial_surjectivity_certificate T a
    (by rw [he]; exact (matrix_mulVec_surjective_iff bM bN _).mpr ha)
  refine ⟨P, hP, fun b hb => ?_⟩
  have h := hp b hb
  rw [he] at h
  exact (matrix_mulVec_surjective_iff bM bN _).mp h

end BPFixedPoints.ResolutionTools
