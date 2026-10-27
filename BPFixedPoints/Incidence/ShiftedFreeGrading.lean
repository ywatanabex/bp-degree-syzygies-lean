import BPFixedPoints.Incidence.GradedSurjectiveImage
import BPFixedPoints.Incidence.CoefficientGrading

/-! # Shifted free modules over a naturally graded coefficient algebra -/

namespace BPFixedPoints.ResolutionTools

open DirectSum Finsupp
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k R J : Type*} [Field k] [CommRing R] [Algebra k R]
  (𝒜 : ℕ → Submodule k R)

/-- Extend the nonnegative grading by zero, without truncated subtraction. -/
noncomputable def gradedIntPiece (q : ℤ) : Submodule k R :=
  if 0 ≤ q then 𝒜 q.toNat else ⊥

@[simp] theorem gradedIntPiece_nat (n : ℕ) : gradedIntPiece 𝒜 n = 𝒜 n := by
  simp [gradedIntPiece]

theorem gradedIntPiece_negative {n : ℤ} (hn : n < 0) : gradedIntPiece 𝒜 n = ⊥ := by
  simp [gradedIntPiece, not_le_of_gt hn]

/-- The coefficient of a generator of weight w has degree q-w. -/
noncomputable def shiftedFreePiece (w : J → ℕ) (q : ℤ) : Submodule k (J →₀ R) where
  carrier := {x | ∀ j, x j ∈ gradedIntPiece 𝒜 (q - (w j : ℤ))}
  zero_mem' := fun j => (gradedIntPiece 𝒜 _).zero_mem
  add_mem' hx hy := fun j => (gradedIntPiece 𝒜 _).add_mem (hx j) (hy j)
  smul_mem' c _ hx := fun j => (gradedIntPiece 𝒜 _).smul_mem c (hx j)

theorem shiftedFreePiece_single (w : J → ℕ) (q : ℤ) (j : J) {r : R}
    (hr : r ∈ gradedIntPiece 𝒜 (q - (w j : ℤ))) : single j r ∈ shiftedFreePiece 𝒜 w q := by
  classical
  intro i
  by_cases h : i = j
  · subst i; simpa using hr
  · rw [single_eq_of_ne h]
    exact (gradedIntPiece 𝒜 _).zero_mem

variable [GradedAlgebra 𝒜]

theorem gradedIntPiece_component (n : ℕ) {m : ℤ} {r : R}
    (hr : r ∈ gradedIntPiece 𝒜 m) :
    GradedRing.proj 𝒜 n r = if (n : ℤ) = m then r else 0 := by
  by_cases hm : 0 ≤ m
  · have hr' : r ∈ 𝒜 m.toNat := by simpa [gradedIntPiece, hm] using hr
    rw [GradedRing.proj_apply, decompose_of_mem 𝒜 hr', DirectSum.coe_of_apply]
    by_cases h : (n : ℤ) = m
    · have he : m.toNat = n := by omega
      simp [h, he]
    · have he : m.toNat ≠ n := by omega
      simp [h, he]
  · have hr0 : r = 0 := by simpa [gradedIntPiece, hm] using hr
    simp [hr0]

theorem gradedIntPiece_mul {x y : R} {m n : ℤ}
    (hx : x ∈ gradedIntPiece 𝒜 m) (hy : y ∈ gradedIntPiece 𝒜 n) :
    x * y ∈ gradedIntPiece 𝒜 (m + n) := by
  by_cases hm : 0 ≤ m
  · by_cases hn : 0 ≤ n
    · have hmn : 0 ≤ m + n := by omega
      have he : (m + n).toNat = m.toNat + n.toNat := by omega
      simp only [gradedIntPiece, if_pos hm] at hx
      simp only [gradedIntPiece, if_pos hn] at hy
      simp only [gradedIntPiece, if_pos hmn, he]
      exact SetLike.GradedMul.mul_mem hx hy
    · have hy0 : y = 0 := by simpa [gradedIntPiece, hn] using hy
      simp only [hy0, mul_zero]
      exact Submodule.zero_mem _
  · have hx0 : x = 0 := by simpa [gradedIntPiece, hm] using hx
    simp only [hx0, zero_mul]
    exact Submodule.zero_mem _

theorem shiftedFreePiece_smul (w : J → ℕ) {r : R} {x : J →₀ R} {n q : ℕ}
    (hr : r ∈ 𝒜 n) (hx : x ∈ shiftedFreePiece 𝒜 w q) :
    r • x ∈ shiftedFreePiece 𝒜 w ((n + q : ℕ) : ℤ) := by
  intro j
  change r * x j ∈ _
  have hr' : r ∈ gradedIntPiece 𝒜 (n : ℤ) := by simpa only [gradedIntPiece_nat] using hr
  simpa only [Nat.cast_add, add_sub_assoc] using gradedIntPiece_mul 𝒜 hr' (hx j)

theorem iSup_shiftedFreePiece (w : J → ℕ) :
    (⨆ q : ℕ, shiftedFreePiece 𝒜 w q) = ⊤ := by
  classical
  let Q := ⨆ q : ℕ, shiftedFreePiece 𝒜 w q
  have hi (j : J) : (⊤ : Submodule k R) ≤
      Q.comap ((lsingle j : R →ₗ[R] (J →₀ R)).restrictScalars k) := by
    rw [← (Decomposition.isInternal 𝒜).submodule_iSup_eq_top]
    apply iSup_le
    intro n r hr
    change single j r ∈ Q
    apply le_iSup (fun q : ℕ => shiftedFreePiece 𝒜 w q) (n + w j)
    apply shiftedFreePiece_single
    have he : ((n + w j : ℕ) : ℤ) - (w j : ℤ) = n := by omega
    simpa only [he, gradedIntPiece_nat] using hr
  apply eq_top_iff.mpr
  intro x _
  rw [← x.sum_single]
  exact Q.sum_mem (fun j _ => hi j (Submodule.mem_top))

theorem shiftedFreePiece_sum_unique (w : J → ℕ) (s : Finset ℕ) (x : ℕ → (J →₀ R))
    (hx : ∀ n ∈ s, x n ∈ shiftedFreePiece 𝒜 w n)
    (hs : ∑ n ∈ s, x n = 0) (q : ℕ) (hq : q ∈ s) : x q = 0 := by
  classical
  ext j
  by_cases hj : w j ≤ q
  · have h := congrArg (fun z => GradedRing.proj 𝒜 (q - w j) (z j)) hs
    simp only [finsetSum_apply, Finsupp.zero_apply, map_sum, map_zero] at h
    have hc (n) (hn : n ∈ s) :
        GradedRing.proj 𝒜 (q - w j) (x n j) = if q = n then x n j else 0 := by
      rw [gradedIntPiece_component _ _ (hx n hn j)]
      have he : ((q - w j : ℕ) : ℤ) = (n : ℤ) - w j ↔ q = n := by omega
      simp only [he]
    rw [Finset.sum_congr rfl hc] at h
    simpa [hq] using h
  · have h := hx q hq j
    rw [gradedIntPiece_negative _ (by omega)] at h
    exact h

theorem iSupIndep_shiftedFreePiece (w : J → ℕ) :
    iSupIndep (fun q : ℕ => shiftedFreePiece 𝒜 w q) :=
  (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr (shiftedFreePiece_sum_unique 𝒜 w)

end BPFixedPoints.ResolutionTools
