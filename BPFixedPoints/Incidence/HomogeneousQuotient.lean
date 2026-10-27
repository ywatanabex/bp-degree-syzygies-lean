import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # The induced grading on the actual quotient by a homogeneous ideal -/

namespace BPFixedPoints.ResolutionTools

open DirectSum
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  (𝒜 : ℕ → Submodule k A) (I : Ideal A)

/-- The degree-q quotient component is the image of the original component. -/
noncomputable def gradedQuotientPiece (q : ℕ) : Submodule k (A ⧸ I) :=
  (𝒜 q).map (Ideal.Quotient.mkₐ k I).toLinearMap

/-- The actual quotient map on each homogeneous component. -/
noncomputable def gradedQuotientMap (q : ℕ) : 𝒜 q →ₗ[k] gradedQuotientPiece 𝒜 I q :=
  ((Ideal.Quotient.mkₐ k I).toLinearMap.domRestrict (𝒜 q)).codRestrict _
    (fun x => Submodule.mem_map.mpr ⟨x.val, x.property, rfl⟩)

theorem gradedQuotientMap_surjective (q : ℕ) :
    Function.Surjective (gradedQuotientMap 𝒜 I q) := by
  intro y
  obtain ⟨x, hx, he⟩ := Submodule.mem_map.mp y.property
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

theorem gradedQuotientPiece_finite (q : ℕ) [Module.Finite k (𝒜 q)] :
    Module.Finite k (gradedQuotientPiece 𝒜 I q) :=
  Module.Finite.of_surjective (gradedQuotientMap 𝒜 I q)
    (gradedQuotientMap_surjective 𝒜 I q)

variable [GradedAlgebra 𝒜]

theorem iSup_gradedQuotientPiece : iSup (gradedQuotientPiece 𝒜 I) = ⊤ := by
  change (⨆ q, (𝒜 q).map (Ideal.Quotient.mkₐ k I).toLinearMap) = ⊤
  rw [← Submodule.map_iSup, (Decomposition.isInternal 𝒜).submodule_iSup_eq_top,
    Submodule.map_top, LinearMap.range_eq_top.mpr]
  exact Ideal.Quotient.mk_surjective

theorem iSupIndep_gradedQuotientPiece (hI : I.IsHomogeneous 𝒜) :
    iSupIndep (gradedQuotientPiece 𝒜 I) := by
  classical
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr
  intro s x hx hsum q hq
  choose y hy he using fun n hn => Submodule.mem_map.mp (hx n hn)
  let z : ℕ → A := fun n => if hn : n ∈ s then y n hn else 0
  have hz (n) (hn : n ∈ s) : z n ∈ 𝒜 n := by simpa [z, hn] using hy n hn
  have hez (n) (hn : n ∈ s) : Ideal.Quotient.mk I (z n) = x n := by
    simpa [z, hn] using he n hn
  have hmem : (∑ n ∈ s, z n) ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sum, Finset.sum_congr rfl hez]
    exact hsum
  have hp := hI q hmem
  change GradedRing.proj 𝒜 q (∑ n ∈ s, z n) ∈ I at hp
  have hc (n) (hn : n ∈ s) : GradedRing.proj 𝒜 q (z n) = if q = n then z n else 0 := by
    rw [GradedRing.proj_apply, decompose_of_mem 𝒜 (hz n hn), DirectSum.coe_of_apply]
    by_cases h : n = q
    · subst n
      simp
    · simp [h, Ne.symm h]
  rw [map_sum, Finset.sum_congr rfl hc] at hp
  have hmemq : z q ∈ I := by simpa [hq] using hp
  rw [← hez q hq]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmemq

/-- The images of the original components form a graded algebra on the quotient. -/
@[instance_reducible]
noncomputable def gradedQuotientAlgebra (hI : I.IsHomogeneous 𝒜) :
    GradedAlgebra (gradedQuotientPiece 𝒜 I) where
  one_mem := by
    exact Submodule.mem_map.mpr ⟨1, SetLike.GradedOne.one_mem, (Ideal.Quotient.mkₐ k I).map_one⟩
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr ⟨a * b, SetLike.GradedMul.mul_mem ha hb,
      (Ideal.Quotient.mkₐ k I).map_mul a b⟩
  __ := (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (iSupIndep_gradedQuotientPiece 𝒜 I hI) (iSup_gradedQuotientPiece 𝒜 I)).chooseDecomposition

/-- The degreewise kernel consists exactly of the elements in the ideal. -/
theorem mem_ker_gradedQuotientMap (q : ℕ) (x : 𝒜 q) :
    x ∈ LinearMap.ker (gradedQuotientMap 𝒜 I q) ↔ x.val ∈ I := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr h)

end BPFixedPoints.ResolutionTools
