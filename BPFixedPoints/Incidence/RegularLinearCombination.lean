import BPFixedPoints.Incidence.RegularSequenceInSubspace
import Mathlib.LinearAlgebra.Pi

/-! # Choosing a regular linear combination with nonzero leading coefficient -/

namespace BPFixedPoints.ResolutionTools

open RingTheory.Sequence
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
universe u

variable {k R : Type u} [Field k] [Infinite k] [CommRing R] [Algebra k R]
  [IsNoetherianRing R]

/-- Finite prime avoidance can retain a nonzero coefficient of the first generator. -/
theorem exists_regular_linear_combination (x : R) (rs : List R)
    (h : ∃ r ∈ Ideal.ofList (x :: rs), IsSMulRegular R r) :
    ∃ c : Fin (rs.length + 1) → k,
      c 0 ≠ 0 ∧ IsSMulRegular R (∑ i, c i • (x :: rs).get i) := by
  classical
  let f : (Fin (rs.length + 1) → k) →ₗ[k] R :=
    ∑ i, (LinearMap.proj i).smulRight ((x :: rs).get i)
  have hf (c) : f c = ∑ i, c i • (x :: rs).get i := by simp [f]
  have hs (i : Fin (rs.length + 1)) : f (Pi.single i 1) = (x :: rs).get i := by
    simp [f, Pi.single_apply]
  have : Finite (associatedPrimes R R) := (associatedPrimes.finite R R).to_subtype
  let Q : Option (associatedPrimes R R) → Submodule k (Fin (rs.length + 1) → k)
    | none => LinearMap.ker (LinearMap.proj 0)
    | some P => (P.val.restrictScalars k).comap f
  have hQ : ∀ P, Q P ≠ ⊤ := by
    intro P he
    cases P with
    | none =>
      have hm : Pi.single (0 : Fin (rs.length + 1)) (1 : k) ∈ Q none := he ▸ Submodule.mem_top
      have hz : (1 : k) = 0 := by simpa [Q, LinearMap.mem_ker] using hm
      exact one_ne_zero hz
    | some P =>
      obtain ⟨r, hr, hreg⟩ := h
      have hle : Ideal.ofList (x :: rs) ≤ P.val := by
        apply Ideal.span_le.mpr
        intro y hy
        obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hy
        have hm : Pi.single i (1 : k) ∈ Q (some P) := he ▸ Submodule.mem_top
        change f (Pi.single i 1) ∈ P.val at hm
        rw [hs] at hm
        exact hm
      exact regular_notMem_associatedPrime R hreg P.property (hle hr)
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top Q hQ
  refine ⟨c, ?_, ?_⟩
  · simpa [Q, LinearMap.mem_ker] using hc none
  · rw [← hf]
    by_contra hn
    have hm : f c ∈ ⋃ P ∈ associatedPrimes R R, (P : Set R) := by
      rw [biUnion_associatedPrimes_eq_compl_regular R R]
      exact hn
    obtain ⟨P, hm⟩ := Set.mem_iUnion.mp hm
    obtain ⟨hP, hm⟩ := Set.mem_iUnion.mp hm
    exact hc (some ⟨P, hP⟩) hm

end BPFixedPoints.ResolutionTools
