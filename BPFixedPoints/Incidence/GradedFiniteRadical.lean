import BPFixedPoints.Incidence.FiniteGradedBound
import Mathlib.RingTheory.Ideal.Operations

/-! # Finite homogeneous quotients and the positive-degree ideal -/

namespace BPFixedPoints.ResolutionTools

open DirectSum
set_option backward.isDefEq.respectTransparency false

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]

/-- A finite homogeneous quotient kills a power of every element of positive degree. -/
theorem irrelevant_le_radical_of_finite_quotient (I : Ideal A) (hI : I.IsHomogeneous 𝒜)
    [Module.Finite k (A ⧸ I)] :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ I.radical := by
  letI := gradedQuotientAlgebra 𝒜 I hI
  obtain ⟨N, hN⟩ := exists_gradedPiece_bound (gradedQuotientPiece 𝒜 I)
  apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
  intro q hq x hx
  apply Ideal.mem_radical_iff.mpr
  refine ⟨N + 1, ?_⟩
  have hp : x ^ (N + 1) ∈ 𝒜 ((N + 1) * q) := by
    simpa using SetLike.pow_mem_graded (A := 𝒜) (N + 1) hx
  have hm : Ideal.Quotient.mk I (x ^ (N + 1)) ∈
      gradedQuotientPiece 𝒜 I ((N + 1) * q) := Submodule.mem_map.mpr ⟨_, hp, rfl⟩
  rw [hN _ (by nlinarith)] at hm
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa using hm

/-- In a graded domain, a finite positive-degree homogeneous quotient has precisely
    the positive-degree ideal as its radical. -/
theorem radical_eq_irrelevant_of_finite_quotient [IsDomain A]
    (I : Ideal A) (hI : I.IsHomogeneous 𝒜)
    (hle : I ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) [Module.Finite k (A ⧸ I)] :
    I.radical = (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
  have hp : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsPrime :=
    RingHom.ker_isPrime (GradedRing.projZeroRingHom 𝒜)
  apply le_antisymm _ (irrelevant_le_radical_of_finite_quotient 𝒜 I hI)
  exact (Ideal.radical_mono hle).trans_eq hp.radical

end BPFixedPoints.ResolutionTools
