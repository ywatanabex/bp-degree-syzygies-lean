import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # A graded surjection with equal component dimensions is an isomorphism -/

namespace BPFixedPoints.ResolutionTools

open DirectSum
set_option backward.isDefEq.respectTransparency false

variable {k M N : Type*} [Field k] [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N]

/-- Equal finite component dimensions upgrade a homogeneous surjection to an isomorphism. -/
theorem bijective_of_graded_surjective_of_finrank_eq
    (𝒜 : ℕ → Submodule k M) (ℬ : ℕ → Submodule k N)
    (hA : DirectSum.IsInternal 𝒜) (hB : DirectSum.IsInternal ℬ)
    [∀ q, Module.Finite k (𝒜 q)] [∀ q, Module.Finite k (ℬ q)]
    (f : M →ₗ[k] N) (hf : ∀ q x, x ∈ 𝒜 q → f x ∈ ℬ q)
    (hs : ∀ q y, y ∈ ℬ q → ∃ x ∈ 𝒜 q, f x = y)
    (hd : ∀ q, Module.finrank k (𝒜 q) = Module.finrank k (ℬ q)) :
    Function.Bijective f := by
  classical
  let g (q : ℕ) : 𝒜 q →ₗ[k] ℬ q := (f.domRestrict (𝒜 q)).codRestrict _
    (fun x => hf q x.val x.property)
  have hgs (q) : Function.Surjective (g q) := by
    intro y
    obtain ⟨x, hx, he⟩ := hs q y.val y.property
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  have hgi (q) : Function.Injective (g q) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hd q)).mpr (hgs q)
  have he : (coeLinearMap ℬ).comp (DirectSum.lmap g) = f.comp (coeLinearMap 𝒜) := by
    ext q x
    simp [g]
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := hA.surjective x
    obtain ⟨b, rfl⟩ := hA.surjective y
    have h : DirectSum.lmap g a = DirectSum.lmap g b := by
      apply hB.injective
      exact (LinearMap.congr_fun he a).trans (hxy.trans (LinearMap.congr_fun he b).symm)
    exact congrArg (coeLinearMap 𝒜) ((DirectSum.lmap_injective g).mpr hgi h)
  · intro y
    obtain ⟨b, rfl⟩ := hB.surjective y
    obtain ⟨a, rfl⟩ := (DirectSum.lmap_surjective g).mpr hgs b
    exact ⟨coeLinearMap 𝒜 a, (LinearMap.congr_fun he a).symm⟩

end BPFixedPoints.ResolutionTools
