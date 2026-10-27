import BPFixedPoints.Family.DimensionTools
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Dimension and transcendence degree of finite-type domains

Use Noether normalization to reduce to an injective integral extension of a
polynomial ring and compute both Krull dimension and transcendence degree.
-/

namespace BPFixedPoints

universe u

/-- The Krull dimension of a finite-type domain over a field equals its transcendence degree. -/
theorem ringKrullDim_eq_trdeg_toNat (k A : Type u) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim A = ((Algebra.trdeg k A).toNat : WithBot ℕ∞) := by
  obtain ⟨n, f, hf, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let N := MvPolynomial (Fin n) k
  let : Algebra N A := f.toRingHom.toAlgebra
  have : IsScalarTower k N A := IsScalarTower.of_algHom f
  have : FaithfulSMul N A := (faithfulSMul_iff_algebraMap_injective N A).mpr hf
  have : Algebra.IsIntegral N A := ⟨hfin.to_isIntegral⟩
  have hdim : ringKrullDim A = (n : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_integral_injective (R := N) (S := A) hf]
    simp [N, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
      ringKrullDim_eq_zero_of_field]
  have htr : Algebra.trdeg k A = n := by
    have h := trdeg_add_eq (A := A) k N
    simpa [N, trdeg_eq_zero (R := N) (A := A)] using h.symm
  rw [hdim, htr, Cardinal.toNat_natCast]

end BPFixedPoints
