import BPFixedPoints.Incidence.HomogeneousQuotient

/-! # The natural image grading under a surjective algebra map -/

namespace BPFixedPoints.ResolutionTools

open DirectSum
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k A R : Type*} [Field k] [CommRing A] [CommRing R] [Algebra k A] [Algebra k R]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] (f : A →ₐ[k] R)

/-- Components are images of the original homogeneous components under the given map. -/
noncomputable def gradedImagePiece (q : ℕ) : Submodule k R := (𝒜 q).map f.toLinearMap

theorem iSup_gradedImagePiece (hf : Function.Surjective f) :
    (⨆ q, gradedImagePiece 𝒜 f q) = ⊤ := by
  change (⨆ q, (𝒜 q).map f.toLinearMap) = ⊤
  rw [← Submodule.map_iSup, (Decomposition.isInternal 𝒜).submodule_iSup_eq_top,
    Submodule.map_top, LinearMap.range_eq_top.mpr hf]

theorem iSupIndep_gradedImagePiece (hker : (RingHom.ker f.toRingHom).IsHomogeneous 𝒜) :
    iSupIndep (gradedImagePiece 𝒜 f) := by
  classical
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr
  intro s x hx hsum q hq
  choose y hy he using fun n hn => Submodule.mem_map.mp (hx n hn)
  let z : ℕ → A := fun n => if hn : n ∈ s then y n hn else 0
  have hz (n) (hn : n ∈ s) : z n ∈ 𝒜 n := by simpa [z, hn] using hy n hn
  have hez (n) (hn : n ∈ s) : f (z n) = x n := by simpa [z, hn] using he n hn
  have hmem : (∑ n ∈ s, z n) ∈ RingHom.ker f.toRingHom := by
    change f (∑ n ∈ s, z n) = 0
    rw [map_sum, Finset.sum_congr rfl hez]
    exact hsum
  have hp := hker q hmem
  change GradedRing.proj 𝒜 q (∑ n ∈ s, z n) ∈ RingHom.ker f.toRingHom at hp
  have hc (n) (hn : n ∈ s) : GradedRing.proj 𝒜 q (z n) = if q = n then z n else 0 := by
    rw [GradedRing.proj_apply, decompose_of_mem 𝒜 (hz n hn), DirectSum.coe_of_apply]
    by_cases h : n = q
    · subst n; simp
    · simp [h, Ne.symm h]
  rw [map_sum, Finset.sum_congr rfl hc] at hp
  have hmemq : z q ∈ RingHom.ker f.toRingHom := by simpa [hq] using hp
  rw [← hez q hq]
  exact hmemq

/-- The original multiplication descends to a graded algebra when the kernel is homogeneous. -/
@[instance_reducible] noncomputable def gradedImageAlgebra
    (hf : Function.Surjective f) (hker : (RingHom.ker f.toRingHom).IsHomogeneous 𝒜) :
    GradedAlgebra (gradedImagePiece 𝒜 f) where
  one_mem := Submodule.mem_map.mpr ⟨1, SetLike.GradedOne.one_mem, f.map_one⟩
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr ⟨a * b, SetLike.GradedMul.mul_mem ha hb, f.map_mul a b⟩
  __ := (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_gradedImagePiece 𝒜 f hker) (iSup_gradedImagePiece 𝒜 f hf)).chooseDecomposition

end BPFixedPoints.ResolutionTools
