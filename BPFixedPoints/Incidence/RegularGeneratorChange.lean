import BPFixedPoints.Incidence.GradedRegularPermutation

/-! # Replacing a homogeneous generator modulo the other generators -/

namespace BPFixedPoints.ResolutionTools

open RingTheory.Sequence
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/-- A change of first generator with nonzero leading scalar preserves its ideal. -/
theorem ofList_head_change {x y : R} {rs : List R} {c : k} (hc : c ≠ 0)
    (hy : y - c • x ∈ Ideal.ofList rs) :
    Ideal.ofList (y :: rs) = Ideal.ofList (x :: rs) := by
  have tail (z : R) : Ideal.ofList rs ≤ Ideal.ofList (z :: rs) := by
    rw [Ideal.ofList_cons]
    exact le_sup_right
  have hx (I : Ideal R) (hi : Ideal.ofList rs ≤ I) (hyI : y ∈ I) : x ∈ I := by
    have hm : c • x ∈ I := by
      simpa only [sub_sub_cancel] using I.sub_mem hyI (hi hy)
    have hu := (I.restrictScalars k).smul_mem c⁻¹ hm
    change c⁻¹ • (c • x) ∈ I at hu
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hu
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · have hxI : x ∈ Ideal.ofList (x :: rs) := Ideal.subset_span (by simp)
      have hm := (Ideal.ofList (x :: rs)).add_mem (tail x hy)
        ((Ideal.ofList (x :: rs)).restrictScalars k |>.smul_mem c hxI)
      change z ∈ Ideal.ofList (x :: rs)
      simpa only [sub_add_cancel] using hm
    · exact tail x (Ideal.subset_span hz)
  · apply Ideal.span_le.mpr
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx _ (tail y) (Ideal.subset_span (by simp))
    · exact tail y (Ideal.subset_span hz)

variable (𝒜 : ℕ → Submodule k R) [GradedAlgebra 𝒜]

/-- Permuting the changed generator to the end reduces the comparison to a quotient. -/
theorem regular_of_homogeneous_head_change {x y : R} {rs : List R} {c : k}
    (hh : ∀ r ∈ x :: rs, r ∈ 𝒜 1) (hy : y ∈ 𝒜 1)
    (hr : IsRegular R (y :: rs)) (hI : Ideal.ofList (x :: rs) ≠ ⊤)
    (he : y - c • x ∈ Ideal.ofList rs) : IsRegular R (x :: rs) := by
  have hyt : ∀ r ∈ y :: rs, r ∈ 𝒜 1 := by
    intro r hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hy
    · exact hh r (by simp [hm])
  have hp : (y :: rs).Perm (rs ++ [y]) := by
    change ([y] ++ rs).Perm (rs ++ [y])
    exact List.perm_append_comm
  have hw := weaklyRegular_of_homogeneous_perm 𝒜 hyt hr.toIsWeaklyRegular hp
  obtain ⟨ht, hyreg⟩ := (isWeaklyRegular_append_iff R rs [y]).mp hw
  rw [isWeaklyRegular_singleton_iff] at hyreg
  let J : Ideal R := Ideal.ofList rs • ⊤
  have hj : J = Ideal.ofList rs := by simp [J]
  have hxreg : IsSMulRegular (R ⧸ J) x := by
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem J x).mpr
    intro z hz
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem J y).mp hyreg z
    have hz' : c • (x * z) ∈ J := (J.restrictScalars k).smul_mem c hz
    have he' : (y - c • x) * z ∈ J := J.mul_mem_right z (hj ▸ he)
    have hm := J.add_mem he' hz'
    change y * z ∈ J
    simpa only [smul_mul_assoc, sub_mul, sub_add_cancel] using hm
  have hwx : IsWeaklyRegular R (rs ++ [x]) :=
    (isWeaklyRegular_append_iff R rs [x]).mpr
      ⟨ht, (isWeaklyRegular_singleton_iff _ x).mpr hxreg⟩
  have hpx : (x :: rs).Perm (rs ++ [x]) := by
    change ([x] ++ rs).Perm (rs ++ [x])
    exact List.perm_append_comm
  have hxhh : ∀ r ∈ rs ++ [x], r ∈ 𝒜 1 := by
    intro r hm
    exact hh r (hpx.mem_iff.mpr hm)
  refine ⟨weaklyRegular_of_homogeneous_perm 𝒜 hxhh hwx hpx.symm, ?_⟩
  simpa using hI.symm

end BPFixedPoints.ResolutionTools
