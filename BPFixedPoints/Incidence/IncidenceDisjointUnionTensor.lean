import Mathlib

/-!
# Intersections of tensor products of subspaces over a field

Over a field `K`, let `T₁` and `T₂` be vector spaces. For subspaces `M ≤ T₁` and `N ≤ T₂` write
`M ⊠ N` for the image of `M ⊗ N` in `T₁ ⊗ T₂`, that is `LinearMap.range (mapIncl M N)`.

This module proves the linear algebra used for the Künneth formula of a disjoint union:
* an element of `T₁ ⊗ T₂` lies in `M ⊠ N` exactly when all its slices by linear functionals on
  either factor lie in `M`, respectively `N` (`mem_range_mapIncl_iff_slices`);
* for nonempty (possibly infinite) families of subspaces,
  `⋂_{i,j} (A_i ⊠ B_j) = (⋂_i A_i) ⊠ (⋂_j B_j)` (`iInf_range_mapIncl`).

The slice criterion uses a basis of each factor and a linear projection onto each subspace, so it
uses that `K` is a field. Nothing is claimed over more general rings.
-/

namespace BPFixedPoints.Multigraph

open TensorProduct

section TensorSlices

variable {K T₁ T₂ : Type*} [Field K] [AddCommGroup T₁] [Module K T₁]
  [AddCommGroup T₂] [Module K T₂]

/-- The slice of a tensor by a linear functional on the right factor. -/
noncomputable def tensorRightSlice (f : T₂ →ₗ[K] K) : T₁ ⊗[K] T₂ →ₗ[K] T₁ :=
  (TensorProduct.rid K T₁).toLinearMap ∘ₗ f.lTensor T₁

/-- The slice of a tensor by a linear functional on the left factor. -/
noncomputable def tensorLeftSlice (g : T₁ →ₗ[K] K) : T₁ ⊗[K] T₂ →ₗ[K] T₂ :=
  (TensorProduct.lid K T₂).toLinearMap ∘ₗ g.rTensor T₂

@[simp] theorem tensorRightSlice_tmul (f : T₂ →ₗ[K] K) (a : T₁) (b : T₂) :
    tensorRightSlice f (a ⊗ₜ[K] b) = f b • a := by
  simp [tensorRightSlice]

@[simp] theorem tensorLeftSlice_tmul (g : T₁ →ₗ[K] K) (a : T₁) (b : T₂) :
    tensorLeftSlice g (a ⊗ₜ[K] b) = g a • b := by
  simp [tensorLeftSlice]

/-- Right slices commute with a linear map on the left factor. -/
theorem tensorRightSlice_rTensor (f : T₂ →ₗ[K] K) (p : T₁ →ₗ[K] T₁) (x : T₁ ⊗[K] T₂) :
    tensorRightSlice f (p.rTensor T₂ x) = p (tensorRightSlice f x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Left slices commute with a linear map on the right factor. -/
theorem tensorLeftSlice_lTensor (g : T₁ →ₗ[K] K) (q : T₂ →ₗ[K] T₂) (x : T₁ ⊗[K] T₂) :
    tensorLeftSlice g (q.lTensor T₁ x) = q (tensorLeftSlice g x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Over a field, a tensor all of whose right slices vanish is zero. -/
theorem eq_zero_of_tensorRightSlice (x : T₁ ⊗[K] T₂)
    (h : ∀ f : T₂ →ₗ[K] K, tensorRightSlice f x = 0) : x = 0 := by
  classical
  let b := Module.Free.chooseBasis K T₂
  apply (equivFinsuppOfBasisRight (M := T₁) b).injective
  ext k
  rw [equivFinsuppOfBasisRight_apply]
  simpa [tensorRightSlice] using h (b.coord k)

/-- Over a field, a tensor all of whose left slices vanish is zero. -/
theorem eq_zero_of_tensorLeftSlice (x : T₁ ⊗[K] T₂)
    (h : ∀ g : T₁ →ₗ[K] K, tensorLeftSlice g x = 0) : x = 0 := by
  classical
  let b := Module.Free.chooseBasis K T₁
  apply (equivFinsuppOfBasisLeft (N := T₂) b).injective
  ext k
  rw [equivFinsuppOfBasisLeft_apply]
  simpa [tensorLeftSlice] using h (b.coord k)

/-- Over a field, every subspace has a linear retraction onto it. -/
theorem exists_submodule_retraction (M : Submodule K T₁) :
    ∃ p : T₁ →ₗ[K] M, ∀ m : M, p m = m := by
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective M.subtype M.ker_subtype
  exact ⟨p, fun m => LinearMap.congr_fun hp m⟩

/-- Slices of an element of `M ⊠ N` lie in `M` and `N`. -/
theorem slices_mem_of_mem_range_mapIncl (M : Submodule K T₁) (N : Submodule K T₂)
    {x : T₁ ⊗[K] T₂} (hx : x ∈ LinearMap.range (mapIncl M N)) :
    (∀ f : T₂ →ₗ[K] K, tensorRightSlice f x ∈ M) ∧
      (∀ g : T₁ →ₗ[K] K, tensorLeftSlice g x ∈ N) := by
  obtain ⟨y, rfl⟩ := hx
  constructor
  · intro f
    induction y using TensorProduct.inductionOn with
    | tmul a b => simpa using M.smul_mem (f b) a.property
    | add x y hx hy => simpa only [map_add] using M.add_mem hx hy
  · intro g
    induction y using TensorProduct.inductionOn with
    | tmul a b => simpa using N.smul_mem (g a) b.property
    | add x y hx hy => simpa only [map_add] using N.add_mem hx hy

/-- **Slice criterion.** Over a field, an element of `T₁ ⊗ T₂` lies in `M ⊠ N` iff all its right
slices lie in `M` and all its left slices lie in `N`. -/
theorem mem_range_mapIncl_iff_slices (M : Submodule K T₁) (N : Submodule K T₂)
    (x : T₁ ⊗[K] T₂) :
    x ∈ LinearMap.range (mapIncl M N) ↔
      (∀ f : T₂ →ₗ[K] K, tensorRightSlice f x ∈ M) ∧
        (∀ g : T₁ →ₗ[K] K, tensorLeftSlice g x ∈ N) := by
  refine ⟨slices_mem_of_mem_range_mapIncl M N, ?_⟩
  rintro ⟨hM, hN⟩
  obtain ⟨p, hp⟩ := exists_submodule_retraction M
  obtain ⟨q, hq⟩ := exists_submodule_retraction N
  have hp' : (M.subtype ∘ₗ p).rTensor T₂ x = x := by
    rw [← sub_eq_zero]
    apply eq_zero_of_tensorRightSlice
    intro f
    rw [map_sub, tensorRightSlice_rTensor, sub_eq_zero]
    exact congrArg Subtype.val (hp ⟨_, hM f⟩)
  have hq' : (N.subtype ∘ₗ q).lTensor T₁ x = x := by
    rw [← sub_eq_zero]
    apply eq_zero_of_tensorLeftSlice
    intro g
    rw [map_sub, tensorLeftSlice_lTensor, sub_eq_zero]
    exact congrArg Subtype.val (hq ⟨_, hN g⟩)
  refine ⟨TensorProduct.map p q x, ?_⟩
  change (mapIncl M N ∘ₗ TensorProduct.map p q) x = x
  rw [mapIncl, ← TensorProduct.map_comp, ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply,
    hq', hp']

/-- **Intersections of tensor products.** Over a field, for nonempty families of subspaces,
`⋂_{i,j} (A_i ⊠ B_j) = (⋂_i A_i) ⊠ (⋂_j B_j)` inside `T₁ ⊗ T₂`. -/
theorem iInf_range_mapIncl {I J : Type*} [Nonempty I] [Nonempty J]
    (A : I → Submodule K T₁) (B : J → Submodule K T₂) :
    ⨅ i, ⨅ j, LinearMap.range (mapIncl (A i) (B j)) =
      LinearMap.range (mapIncl (⨅ i, A i) (⨅ j, B j)) := by
  apply le_antisymm
  · intro x hx
    simp only [Submodule.mem_iInf] at hx
    rw [mem_range_mapIncl_iff_slices]
    refine ⟨fun f => Submodule.mem_iInf _ |>.2 fun i => ?_,
      fun g => Submodule.mem_iInf _ |>.2 fun j => ?_⟩
    · exact (slices_mem_of_mem_range_mapIncl _ _ (hx i (Classical.arbitrary J))).1 f
    · exact (slices_mem_of_mem_range_mapIncl _ _ (hx (Classical.arbitrary I) j)).2 g
  · exact le_iInf₂ fun i j => range_mapIncl_mono (iInf_le _ i) (iInf_le _ j)

/-- Membership form of `iInf_range_mapIncl`. -/
theorem mem_range_mapIncl_iInf_iff {I J : Type*} [Nonempty I] [Nonempty J]
    (A : I → Submodule K T₁) (B : J → Submodule K T₂) (x : T₁ ⊗[K] T₂) :
    x ∈ LinearMap.range (mapIncl (⨅ i, A i) (⨅ j, B j)) ↔
      ∀ i j, x ∈ LinearMap.range (mapIncl (A i) (B j)) := by
  rw [← iInf_range_mapIncl]
  simp only [Submodule.mem_iInf]

end TensorSlices

end BPFixedPoints.Multigraph
