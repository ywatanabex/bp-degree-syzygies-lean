import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.MvPolynomial.Eval

/-! # A polynomial certificate for persistence of surjectivity

A right inverse at one parameter value produces a square determinant. Its nonvanishing
guarantees surjectivity of the original, possibly rectangular, polynomial matrix.
-/

namespace BPFixedPoints.ResolutionTools

open MvPolynomial Matrix
set_option backward.isDefEq.respectTransparency false

variable {k σ m n : Type*} [Field k] [Fintype m] [Fintype n] [DecidableEq m]

theorem exists_polynomial_surjectivity_certificate (M : Matrix m n (MvPolynomial σ k))
    (a : σ → k) (ha : Function.Surjective (M.map (eval a)).mulVec) :
    ∃ P : MvPolynomial σ k, eval a P ≠ 0 ∧
      ∀ b : σ → k, eval b P ≠ 0 → Function.Surjective (M.map (eval b)).mulVec := by
  classical
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp ha
  let P := (M * B.map C).det
  have he (b : σ → k) : eval b P = ((M.map (eval b)) * B).det := by
    rw [show P = (M * B.map C).det from rfl, (eval b).map_det,
      RingHom.mapMatrix_apply, Matrix.map_mul]
    congr 2
    ext i j
    simp
  refine ⟨P, ?_, fun b hb => ?_⟩
  · rw [he, hB, Matrix.det_one]
    exact one_ne_zero
  · rw [he] at hb
    have hs : Function.Surjective ((M.map (eval b)) * B).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hb))
    intro y
    obtain ⟨x, hx⟩ := hs y
    exact ⟨B *ᵥ x, by simpa only [Matrix.mulVec_mulVec] using hx⟩

end BPFixedPoints.ResolutionTools
