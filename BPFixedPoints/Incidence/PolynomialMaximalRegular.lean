import BPFixedPoints.Incidence.PolynomialRegularSequence
import Mathlib.RingTheory.Nullstellensatz

/-! # Maximal-length regular sequences in polynomial maximal ideals -/

namespace BPFixedPoints.ResolutionTools

open MvPolynomial RingTheory.Sequence
set_option backward.isDefEq.respectTransparency false
universe u

variable {k σ : Type u} [CommRing k]

/-- Polynomial-ring automorphism translating coordinates by x. -/
noncomputable def polynomialTranslation (x : σ → k) :
    MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  AlgEquiv.ofAlgHom (aeval (fun i => X i - C (x i)))
    (aeval (fun i => X i + C (x i)))
    (by ext i; simp) (by ext i; simp)

@[simp] theorem aeval_polynomialTranslation (x : σ → k) (p : MvPolynomial σ k) :
    aeval x (polynomialTranslation x p) = constantCoeff p := by
  have h : (aeval x).comp (polynomialTranslation x).toAlgHom =
      aeval (fun _ : σ => (0 : k)) := by
    ext i
    simp [polynomialTranslation]
  have hp := congrArg (fun f : MvPolynomial σ k →ₐ[k] k => f p) h
  simpa using hp

/-- Every maximal ideal in a finite-variable polynomial ring over an algebraically closed field contains a regular sequence of length equal to the number of variables. -/
theorem exists_regular_sequence_in_maximal_mvPolynomial
    (k : Type u) [Field k] [IsAlgClosed k] (σ : Type u) [Finite σ]
    (I : Ideal (MvPolynomial σ k)) [I.IsMaximal] :
    ∃ rs : List (MvPolynomial σ k), rs.length = Nat.card σ ∧
      (∀ r ∈ rs, r ∈ I) ∧ IsRegular (MvPolynomial σ k) rs := by
  obtain ⟨x, hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal k (I := I) inferInstance
  obtain ⟨rs, hlen, hmem, hreg⟩ := exists_regular_sequence_mvPolynomial k σ
  refine ⟨rs.map (polynomialTranslation x), by simpa using hlen, ?_,
    isRegular_map_ringEquiv (polynomialTranslation x).toRingEquiv rs hreg⟩
  intro r hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  rw [hx, mem_vanishingIdeal_singleton_iff, aeval_polynomialTranslation]
  exact hmem p hp

end BPFixedPoints.ResolutionTools
