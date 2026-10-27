import BPFixedPoints.Incidence.HomogeneousQuotient
import Mathlib.Algebra.Module.Submodule.Pointwise

/-! # Separation by powers of a positive-degree element -/

namespace BPFixedPoints.ResolutionTools

open DirectSum
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

variable {k R A : Type*} [Field k] [CommRing R] [CommRing A]
  [Algebra k A] [Algebra R A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]

/-- An element divisible by all powers of a homogeneous element of degree one is zero. -/
theorem eq_zero_of_divisible_by_all_homogeneous_powers {r x : A} (hr : r ∈ 𝒜 1)
    (hx : ∀ n : ℕ, ∃ y : A, r ^ n * y = x) : x = 0 := by
  apply (decompose 𝒜).injective
  apply DFinsupp.ext
  intro q
  apply Subtype.ext
  obtain ⟨y, hy⟩ := hx (q + 1)
  have hp : r ^ (q + 1) ∈ 𝒜 (q + 1) := by
    simpa using SetLike.pow_mem_graded (A := 𝒜) (q + 1) hr
  simp only [decompose_zero, DFinsupp.zero_apply, ZeroMemClass.coe_zero]
  rw [← hy]
  exact coe_decompose_mul_of_left_mem_of_not_le 𝒜 hp (by omega)

/-- Positive-degree scalar multiplication cannot act surjectively on a nonzero submodule. -/
theorem submodule_eq_bot_of_eq_homogeneous_smul (K : Submodule R A) (r : R)
    (hr : algebraMap R A r ∈ 𝒜 1) (h : K = r • K) : K = ⊥ := by
  have hn (n : ℕ) : K = r ^ n • K := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, ← h, ← ih]
  apply (Submodule.eq_bot_iff K).mpr
  intro x hx
  apply eq_zero_of_divisible_by_all_homogeneous_powers 𝒜 hr
  intro n
  have hm : x ∈ r ^ n • K := hn n ▸ hx
  obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists x (r ^ n) K).mp hm
  exact ⟨y, by simpa only [Algebra.smul_def, map_pow] using hy⟩

end BPFixedPoints.ResolutionTools
