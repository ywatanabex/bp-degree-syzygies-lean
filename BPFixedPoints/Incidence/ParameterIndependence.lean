import BPFixedPoints.Incidence.DimensionTools
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-! # Finite polynomial parameters of full dimension are algebraically independent -/

namespace BPFixedPoints.ResolutionTools

open scoped nonZeroDivisors
set_option backward.isDefEq.respectTransparency false

universe u
variable {k A : Type u} [Field k] [CommRing A]
  [Algebra k A] (n : ℕ)

/-- A finite map from an n-variable polynomial ring to a ring of dimension n is injective. -/
theorem polynomial_finite_injective_of_dimension
    (f : MvPolynomial (Fin n) k →ₐ[k] A) (hf : f.toRingHom.Finite)
    (hd : ringKrullDim A = (n : WithBot ℕ∞)) : Function.Injective f := by
  let S := MvPolynomial (Fin n) k
  letI : Algebra S A := f.toRingHom.toAlgebra
  haveI : Module.Finite S A := hf
  let I := RingHom.ker f.toRingHom
  let Q := S ⧸ I
  letI : Algebra Q A := (RingHom.kerLift f.toRingHom).toAlgebra
  haveI : IsScalarTower S Q A :=
    IsScalarTower.of_algebraMap_eq (R := S) (S := Q) (A := A) (fun _ => rfl)
  haveI : Algebra.IsIntegral Q A :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := S) x).tower_top⟩
  have hQ : ringKrullDim Q = (n : WithBot ℕ∞) := by
    rw [← ringKrullDim_eq_of_integral_injective (RingHom.kerLift_injective f.toRingHom)]
    exact hd
  apply (RingHom.injective_iff_ker_eq_bot f.toRingHom).mpr
  by_contra h
  obtain ⟨r, hr, hn⟩ := (Submodule.ne_bot_iff _).mp h
  have hle := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hn)
    (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
  change ringKrullDim Q + 1 ≤ ringKrullDim S at hle
  rw [hQ] at hle
  have hS : ringKrullDim S = (n : WithBot ℕ∞) := by
    simp [S, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field]
  rw [hS] at hle
  have hn' : n + 1 ≤ n := by exact_mod_cast hle
  omega

end BPFixedPoints.ResolutionTools
