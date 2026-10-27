import Mathlib.RingTheory.Depth.Basic

/-! # Depth under a surjective change of the acting ring -/

namespace BPFixedPoints.ResolutionTools

open CategoryTheory RingTheory.Sequence
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
universe u

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- The same scalar actions give the same regular sequence before and after a ring map. -/
theorem regular_map_algebraMap_iff (rs : List R) :
    IsRegular M rs ↔ IsRegular M (rs.map (algebraMap R S)) := by
  apply AddEquiv.isRegular_congr (e := AddEquiv.refl M)
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro r _ x
  exact (IsScalarTower.algebraMap_smul S r x).symm

/-- A list in the image of an ideal lifts term by term to that ideal. -/
theorem exists_list_in_ideal_map (f : R →+* S) (hf : Function.Surjective f) (I : Ideal R)
    (rs : List S) (hrs : ∀ r ∈ rs, r ∈ I.map f) :
    ∃ xs : List R, xs.map f = rs ∧ ∀ x ∈ xs, x ∈ I := by
  induction rs with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons r rs ih =>
    obtain ⟨x, hx, he⟩ := (Ideal.mem_map_iff_of_surjective f hf).mp (hrs r (by simp))
    obtain ⟨xs, hxs, hmem⟩ := ih (fun y hy => hrs y (by simp [hy]))
    refine ⟨x :: xs, by simp [he, hxs], ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact hmem y hy

/-- Ideal depth is unchanged under a surjective change of the acting ring. -/
theorem depth_map_of_surjective [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Finite R M] [Module.Finite S M]
    (hf : Function.Surjective (algebraMap R S)) (I : Ideal R)
    (hI : I • (⊤ : Submodule R M) < ⊤)
    (hJ : I.map (algebraMap R S) • (⊤ : Submodule S M) < ⊤) :
    I.depth (ModuleCat.of R M) = (I.map (algebraMap R S)).depth (ModuleCat.of S M) := by
  rw [Ideal.depth_eq_sSup_length_isRegular I (ModuleCat.of R M) hI,
    Ideal.depth_eq_sSup_length_isRegular _ (ModuleCat.of S M) hJ]
  apply le_antisymm
  · apply sSup_le
    rintro n ⟨rs, hr, hm, rfl⟩
    apply le_sSup
    refine ⟨rs.map (algebraMap R S), (regular_map_algebraMap_iff (M := M) rs).mp hr, ?_, by simp⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact Ideal.mem_map_of_mem _ (hm x hx)
  · apply sSup_le
    rintro n ⟨rs, hr, hm, rfl⟩
    obtain ⟨xs, hxs, hx⟩ := exists_list_in_ideal_map (algebraMap R S) hf I rs hm
    have hreg : IsRegular M xs := (regular_map_algebraMap_iff (M := M) xs).mpr (hxs ▸ hr)
    have hlen : xs.length = rs.length := by simpa using congrArg List.length hxs
    exact le_sSup ⟨xs, hreg, hx, by simp [hlen]⟩

end BPFixedPoints.ResolutionTools
