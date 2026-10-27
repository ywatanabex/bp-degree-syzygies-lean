import BPFixedPoints.Incidence.HomogeneousQuotient
import Mathlib.RingTheory.Ideal.Maximal

/-! # The homogeneous origin of a connected graded algebra -/

namespace BPFixedPoints.ResolutionTools

open DirectSum
set_option backward.isDefEq.respectTransparency false

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] [Nontrivial A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]

/-- If degree zero consists of scalars, the positive-degree ideal is maximal. -/
theorem irrelevant_isMaximal_of_degree_zero
    (h0 : ∀ x ∈ 𝒜 0, ∃ c : k, algebraMap k A c = x) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsMaximal := by
  let π := GradedRing.projZeroRingHom 𝒜
  have hπ (x : A) : π (π x) = π x :=
    decompose_of_mem_same 𝒜 (decompose 𝒜 x 0).property
  apply Ideal.isMaximal_iff.mpr
  refine ⟨?_, fun J x hle hx hxJ => ?_⟩
  · change π 1 ≠ 0
    rw [map_one]
    exact one_ne_zero
  · change π x ≠ 0 at hx
    obtain ⟨c, hc⟩ := h0 (π x) (decompose 𝒜 x 0).property
    have hc0 : c ≠ 0 := by
      intro h
      apply hx
      rw [← hc, h, map_zero]
    have hm : x - π x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
      change π (x - π x) = 0
      rw [map_sub, hπ, sub_self]
    have hcJ : algebraMap k A c ∈ J := by
      rw [hc]
      simpa using J.sub_mem hxJ (hle hm)
    have hu := (J.restrictScalars k).smul_mem c⁻¹ hcJ
    change c⁻¹ • algebraMap k A c ∈ J at hu
    simpa only [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc0, map_one] using hu

end BPFixedPoints.ResolutionTools
