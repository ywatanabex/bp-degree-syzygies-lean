import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Alternating dimension formula for augmented exact sequences -/

namespace BPFixedPoints.ResolutionTools

variable {k N : Type*} [Field k] [AddCommMonoid N] [Module k N]
  (M : ℕ → Type*) [∀ p, AddCommMonoid (M p)] [∀ p, Module k (M p)]
  [∀ p, Module.Finite k (M p)]
  (d : ∀ p, M (p + 1) →ₗ[k] M p) (ε : M 0 →ₗ[k] N)
  (hex : ∀ p, LinearMap.range (d (p + 1)) = LinearMap.ker (d p))
  (hzero : LinearMap.range (d 0) = LinearMap.ker ε)
  (hsurj : Function.Surjective ε)

include hex hzero hsurj

/-- A finite truncated Euler sum retains the dimension of the last image as a boundary term. -/
theorem alternating_finrank_exact_partial (n : ℕ) :
    (∑ p ∈ Finset.range (n + 1), (-1 : ℤ) ^ p * Module.finrank k (M p)) =
      Module.finrank k N + (-1 : ℤ) ^ n * Module.finrank k (LinearMap.range (d n)) := by
  letI : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  letI : ∀ p, AddCommGroup (M p) := fun p => Module.addCommMonoidToAddCommGroup k
  have h₀ : Module.finrank k N + Module.finrank k (LinearMap.range (d 0)) =
      Module.finrank k (M 0) := by
    rw [hzero, ← ε.finrank_range_add_finrank_ker, LinearMap.range_eq_top.mpr hsurj]
    simp
  have hd (p : ℕ) : Module.finrank k (LinearMap.range (d p)) +
      Module.finrank k (LinearMap.range (d (p + 1))) = Module.finrank k (M (p + 1)) := by
    rw [hex p]
    exact (d p).finrank_range_add_finrank_ker
  induction n with
  | zero => simpa using (congrArg (fun r : ℕ => (r : ℤ)) h₀).symm
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have h := congrArg (fun r : ℕ => (r : ℤ)) (hd n)
    simp only [Nat.cast_add] at h
    rw [← h]
    ring

/-- If the exact sequence vanishes in the next degree, its alternating sum is the actual dimension of the augmentation target. -/
theorem alternating_finrank_exact (n : ℕ) (hn : Module.finrank k (M (n + 1)) = 0) :
    (Module.finrank k N : ℤ) =
      ∑ p ∈ Finset.range (n + 1), (-1 : ℤ) ^ p * Module.finrank k (M p) := by
  have hz : Module.finrank k (LinearMap.range (d n)) = 0 := by
    have h := (d n).finrank_range_le
    rw [hn] at h
    exact Nat.eq_zero_of_le_zero h
  rw [alternating_finrank_exact_partial M d ε hex hzero hsurj n, hz]
  simp

end BPFixedPoints.ResolutionTools
