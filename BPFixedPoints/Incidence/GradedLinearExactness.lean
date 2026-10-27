import Mathlib.LinearAlgebra.DFinsupp

/-!
# Homogeneous images and exactness

If source graded pieces span and target pieces are independent, a homogeneous
image has a preimage of the same degree. This supports both ring-grading
comparison and exactness in each degree.
-/

namespace BPFixedPoints.ResolutionTools

variable {k M N : Type*} [CommRing k] [AddCommGroup M] [Module k M]
  [AddCommGroup N] [Module k N]

theorem exists_homogeneous_preimage (P : ℕ → Submodule k M) (Q : ℕ → Submodule k N)
    (hP : iSup P = ⊤) (hQ : iSupIndep Q) (f : M →ₗ[k] N)
    (hf : ∀ n x, x ∈ P n → f x ∈ Q n) (q : ℕ) {y : N} (hy : y ∈ Q q)
    (hyf : y ∈ LinearMap.range f) : ∃ x, x ∈ P q ∧ f x = y := by
  classical
  obtain ⟨x, hx⟩ := hyf
  obtain ⟨g, hg, he⟩ := (Submodule.mem_iSup_iff_exists_finsupp P x).mp (by rw [hP]; trivial)
  let s := insert q g.support
  have hsum : ∑ n ∈ s, g n = x := by
    rw [← he, Finsupp.sum]
    symm
    apply Finset.sum_subset (Finset.subset_insert _ _)
    intro n _ hn
    exact Finsupp.notMem_support_iff.mp hn
  let v := fun n => f (g n) - if n = q then y else 0
  have hv (n : ℕ) (_ : n ∈ s) : v n ∈ Q n := by
    apply (Q n).sub_mem (hf n (g n) (hg n))
    split_ifs with h
    · subst n; exact hy
    · exact (Q n).zero_mem
  have hvsum : ∑ n ∈ s, v n = 0 := by
    simp only [v, Finset.sum_sub_distrib, ← map_sum, hsum, hx]
    simp [s]
  have hz := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero Q).mp hQ s v hv hvsum q
    (Finset.mem_insert_self _ _)
  exact ⟨g q, hg q, sub_eq_zero.mp (by simpa [v] using hz)⟩

end BPFixedPoints.ResolutionTools
