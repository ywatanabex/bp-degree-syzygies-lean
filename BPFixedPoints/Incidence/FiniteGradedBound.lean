import BPFixedPoints.Incidence.HomogeneousQuotient
import Mathlib.Order.CompactlyGenerated.Basic

/-! # A finite-dimensional graded algebra has bounded homogeneous support -/

namespace BPFixedPoints.ResolutionTools

open DirectSum

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]

/-- Directness of the grading forces only finitely many nonzero pieces. -/
theorem exists_gradedPiece_bound [Module.Finite k A] :
    ∃ N : ℕ, ∀ q, N ≤ q → 𝒜 q = ⊥ := by
  classical
  have hf : {q | 𝒜 q ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep (Decomposition.isInternal 𝒜).submodule_iSupIndep
  refine ⟨hf.toFinset.sup id + 1, fun q hq => ?_⟩
  by_contra hn
  have hm : q ∈ hf.toFinset := hf.mem_toFinset.mpr hn
  have he : q ≤ hf.toFinset.sup id := Finset.le_sup (f := id) hm
  omega

/-- Finiteness of an actual homogeneous quotient gives a vanishing positive component. -/
theorem exists_gradedQuotientPiece_zero (I : Ideal A) (hI : I.IsHomogeneous 𝒜)
    [Module.Finite k (A ⧸ I)] :
    ∃ q : ℕ, gradedQuotientPiece 𝒜 I (q + 1) = ⊥ := by
  letI := gradedQuotientAlgebra 𝒜 I hI
  obtain ⟨N, hN⟩ := exists_gradedPiece_bound (gradedQuotientPiece 𝒜 I)
  exact ⟨N, hN _ (Nat.le_succ N)⟩

end BPFixedPoints.ResolutionTools
