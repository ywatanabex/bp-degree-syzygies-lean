import BPFixedPoints.Incidence.GradedSeparation
import Mathlib.RingTheory.Regular.RegularSequence

/-! # Permuting homogeneous regular sequences

Separation by positive-degree powers replaces the local Nakayama argument.
-/

namespace BPFixedPoints.ResolutionTools

open RingTheory.Sequence
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]

/-- A list of homogeneous degree-one elements generates a homogeneous ideal. -/
theorem homogeneous_ofList {rs : List A} (hh : ∀ r ∈ rs, r ∈ 𝒜 1) :
    (Ideal.ofList rs).IsHomogeneous 𝒜 := by
  apply Ideal.homogeneous_span 𝒜
  intro r hr
  exact ⟨1, hh r hr⟩

/-- Weak regularity of degree-one elements is preserved by every permutation. -/
theorem weaklyRegular_of_homogeneous_perm {rs rs' : List A}
    (hh : ∀ r ∈ rs, r ∈ 𝒜 1) (hr : IsWeaklyRegular A rs) (hp : rs.Perm rs') :
    IsWeaklyRegular A rs' := by
  apply hr.prototype_perm hp
  intro a b xs hs K hK
  let J : Ideal A := Ideal.ofList xs • ⊤
  have hJ : J.IsHomogeneous 𝒜 := by
    have he : J = Ideal.ofList xs := by simp [J]
    rw [he]
    exact homogeneous_ofList 𝒜 (fun x hx => hh x (hs.subset (by simp [hx])))
  letI := gradedQuotientAlgebra 𝒜 J hJ
  apply submodule_eq_bot_of_eq_homogeneous_smul (gradedQuotientPiece 𝒜 J) K a _ hK
  exact Submodule.mem_map.mpr ⟨a, hh a (hs.subset (by simp)), rfl⟩

/-- Regularity of degree-one elements is preserved by every permutation. -/
theorem regular_of_homogeneous_perm {rs rs' : List A}
    (hh : ∀ r ∈ rs, r ∈ 𝒜 1) (hr : IsRegular A rs) (hp : rs.Perm rs') :
    IsRegular A rs' := by
  refine ⟨weaklyRegular_of_homogeneous_perm 𝒜 hh hr.toIsWeaklyRegular hp, ?_⟩
  have he : Ideal.ofList rs' = Ideal.ofList rs := by
    apply congrArg Ideal.span
    exact Set.ext (fun x => hp.mem_iff.symm)
  simpa only [he] using hr.top_ne_smul

end BPFixedPoints.ResolutionTools
