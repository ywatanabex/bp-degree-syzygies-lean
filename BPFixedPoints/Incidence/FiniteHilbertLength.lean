import BPFixedPoints.Incidence.RegularLinearHilbert
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Dimension from a polynomial Hilbert series -/

namespace BPFixedPoints.ResolutionTools

open DirectSum
open scoped PowerSeries
set_option backward.isDefEq.respectTransparency false

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] [∀ q, Module.Finite k (𝒜 q)]

theorem gradedPiece_eq_bot_of_hilbert_coeff_zero (p : Polynomial ℤ)
    (h : gradedHilbertSeries 𝒜 = (p : PowerSeries ℤ)) (q : ℕ) (hq : p.coeff q = 0) :
    𝒜 q = ⊥ := by
  have hc := congrArg (PowerSeries.coeff q) h
  simp only [gradedHilbertSeries, PowerSeries.coeff_mk, Polynomial.coeff_coe, hq,
    Nat.cast_eq_zero] at hc
  exact Submodule.finrank_eq_zero.mp hc

theorem finrank_eq_sum_of_graded_bound (N : ℕ) (hN : ∀ q, N ≤ q → 𝒜 q = ⊥) :
    Module.finrank k A = ∑ q ∈ Finset.range N, Module.finrank k (𝒜 q) := by
  classical
  let ℬ : Fin N → Submodule k A := fun q => 𝒜 q.val
  have hind : iSupIndep ℬ := (Decomposition.isInternal 𝒜).submodule_iSupIndep.comp Fin.val_injective
  have hsup : iSup ℬ = ⊤ := by
    apply top_unique
    rw [← (Decomposition.isInternal 𝒜).submodule_iSup_eq_top]
    apply iSup_le
    intro q
    by_cases hq : q < N
    · exact le_iSup ℬ ⟨q, hq⟩
    · rw [hN q (by omega)]
      exact bot_le
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap ℬ)
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup)
  rw [← e.finrank_eq, Module.finrank_directSum]
  exact Fin.sum_univ_eq_sum_range (fun q => Module.finrank k (𝒜 q)) N

/-- Evaluation at one is justified by the actual finite homogeneous decomposition. -/
theorem finrank_eq_eval_one_of_hilbert_polynomial (p : Polynomial ℤ)
    (h : gradedHilbertSeries 𝒜 = (p : PowerSeries ℤ)) :
    (Module.finrank k A : ℤ) = p.eval 1 := by
  have hN : ∀ q, p.natDegree + 1 ≤ q → 𝒜 q = ⊥ := by
    intro q hq
    exact gradedPiece_eq_bot_of_hilbert_coeff_zero 𝒜 p h q
      (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))
  rw [finrank_eq_sum_of_graded_bound 𝒜 (p.natDegree + 1) hN, Nat.cast_sum,
    Polynomial.eval_eq_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  have hc := congrArg (PowerSeries.coeff q) h
  simpa only [gradedHilbertSeries, PowerSeries.coeff_mk, Polynomial.coeff_coe,
    one_pow, mul_one] using hc

/-- The same dimension formula for the induced grading on an actual quotient. -/
theorem finrank_quotient_eq_eval_one_of_hilbert_polynomial (I : Ideal A)
    (hI : I.IsHomogeneous 𝒜) (p : Polynomial ℤ)
    (h : gradedHilbertSeries (gradedQuotientPiece 𝒜 I) = (p : PowerSeries ℤ)) :
    (Module.finrank k (A ⧸ I) : ℤ) = p.eval 1 := by
  letI := gradedQuotientAlgebra 𝒜 I hI
  letI : ∀ q, Module.Finite k (gradedQuotientPiece 𝒜 I q) :=
    fun q => gradedQuotientPiece_finite 𝒜 I q
  exact finrank_eq_eval_one_of_hilbert_polynomial (gradedQuotientPiece 𝒜 I) p h

end BPFixedPoints.ResolutionTools
