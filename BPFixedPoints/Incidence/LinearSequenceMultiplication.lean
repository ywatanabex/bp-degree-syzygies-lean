import BPFixedPoints.Incidence.RegularLinearHilbert
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Homogeneous multiplication by a finite sequence of linear forms -/

namespace BPFixedPoints.ResolutionTools

open DirectSum
set_option backward.isDefEq.respectTransparency false

variable {k A ι : Type*} [Field k] [CommRing A] [Algebra k A] [Fintype ι]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]

/-- Multiplication by a tuple of linear forms in a fixed homogeneous degree. -/
noncomputable def linearSequenceMultiply (x : ι → A) (hx : ∀ i, x i ∈ 𝒜 1) (q : ℕ) :
    (ι → 𝒜 q) →ₗ[k] 𝒜 (q + 1) :=
  ∑ i, (gradedLinearMultiply 𝒜 (hx i) q).comp (LinearMap.proj i)

theorem linearSequenceMultiply_apply (x : ι → A) (hx : ∀ i, x i ∈ 𝒜 1)
    (q : ℕ) (y : ι → 𝒜 q) :
    (linearSequenceMultiply 𝒜 x hx q y).val = ∑ i, x i * (y i).val := by
  simp [linearSequenceMultiply, gradedLinearMultiply]

theorem range_linearSequenceMultiply (x : ι → A) (hx : ∀ i, x i ∈ 𝒜 1) (q : ℕ) :
    LinearMap.range (linearSequenceMultiply 𝒜 x hx q) =
      LinearMap.ker (gradedQuotientMap 𝒜 (Ideal.span (Set.range x)) (q + 1)) := by
  classical
  ext y
  rw [mem_ker_gradedQuotientMap]
  constructor
  · rintro ⟨z, rfl⟩
    rw [linearSequenceMultiply_apply]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self i)))
  · intro hy
    obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hy
    refine ⟨fun i => decompose 𝒜 (z i) q, Subtype.ext ?_⟩
    rw [linearSequenceMultiply_apply]
    have h := congrArg (GradedRing.proj 𝒜 (q + 1)) hz
    rw [map_sum, GradedRing.proj_apply, decompose_of_mem_same 𝒜 y.property] at h
    have he (i) : GradedRing.proj 𝒜 (q + 1) (z i • x i) =
        x i * decompose 𝒜 (z i) q := by
      change (decompose 𝒜 (z i * x i) (q + 1) : A) = _
      rw [mul_comm, Nat.add_comm q 1, coe_decompose_mul_add_of_left_mem 𝒜 (hx i)]
    simpa only [he] using h

theorem linearSequenceMultiply_surjective_of_piece_zero
    (x : ι → A) (hx : ∀ i, x i ∈ 𝒜 1) (q : ℕ)
    (hz : gradedQuotientPiece 𝒜 (Ideal.span (Set.range x)) (q + 1) = ⊥) :
    Function.Surjective (linearSequenceMultiply 𝒜 x hx q) := by
  apply LinearMap.range_eq_top.mp
  rw [range_linearSequenceMultiply]
  haveI : Subsingleton (gradedQuotientPiece 𝒜 (Ideal.span (Set.range x)) (q + 1)) := by
    rw [hz]
    infer_instance
  exact LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)

end BPFixedPoints.ResolutionTools
