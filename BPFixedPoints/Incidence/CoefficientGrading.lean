import BPFixedPoints.Incidence.CoefficientMatrices
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The coefficient grading of shifted free polynomial modules

Negative coefficient degrees are zero. Thus no truncated natural-number
subtraction can silently identify an impossible degree with degree zero.
The grading is over the ground field, not over the polynomial ring.
-/

namespace BPFixedPoints.ResolutionTools

open Finsupp

section Coefficients

variable {k R I J : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- A ground-ring submodule imposed separately on every coefficient. -/
def coefficientwise (P : Submodule k R) : Submodule k (I →₀ R) where
  carrier := {x | ∀ i, x i ∈ P}
  zero_mem' := fun _ => P.zero_mem
  add_mem' hx hy := fun i => P.add_mem (hx i) (hy i)
  smul_mem' c _ hx := fun i => P.smul_mem c (hx i)

/-- A constant-entry matrix preserves every ground-ring submodule of
coefficients. This does not hold for a general polynomial-linear map. -/
theorem MatrixOver.preserve_coefficients
    {f : (I →₀ R) →ₗ[R] (J →₀ R)}
    (hf : MatrixOver (algebraMap k R).range f)
    (P : Submodule k R) {x : I →₀ R} (hx : x ∈ coefficientwise P) :
    f x ∈ coefficientwise P := by
  rw [← x.sum_single, map_finsuppSum]
  apply (coefficientwise P).sum_mem
  intro i hi
  change f (single i (x i)) ∈ coefficientwise P
  have he : single i (x i) = x i • single i (1 : R) := by simp
  rw [he, map_smul]
  intro j
  obtain ⟨c, hc⟩ := hf i j
  change x i * f (single i 1) j ∈ P
  rw [← hc, mul_comm]
  simpa only [Algebra.smul_def] using P.smul_mem c (hx i)

end Coefficients

section Polynomial

variable {σ k : Type*} [CommRing k]

/-- The usual homogeneous coefficient subspace, with zero negative pieces. -/
noncomputable def homogeneousCoeffPiece (n : ℤ) : Submodule k (MvPolynomial σ k) :=
  if 0 ≤ n then MvPolynomial.homogeneousSubmodule σ k n.toNat else ⊥

theorem homogeneousCoeffPiece_nat (n : ℕ) :
    homogeneousCoeffPiece (σ := σ) (k := k) (n : ℤ) =
      MvPolynomial.homogeneousSubmodule σ k n := by
  simp [homogeneousCoeffPiece]

theorem homogeneousCoeffPiece_negative {n : ℤ} (hn : n < 0) :
    homogeneousCoeffPiece (σ := σ) (k := k) n = ⊥ := by
  simp [homogeneousCoeffPiece, not_le_of_gt hn]

theorem homogeneousCoeffPiece_mul {x y : MvPolynomial σ k} {m n : ℤ}
    (hx : x ∈ homogeneousCoeffPiece m) (hy : y ∈ homogeneousCoeffPiece n) :
    x * y ∈ homogeneousCoeffPiece (m + n) := by
  by_cases hm : 0 ≤ m
  · by_cases hn : 0 ≤ n
    · have hmn : 0 ≤ m + n := by omega
      have hnat : (m + n).toNat = m.toNat + n.toNat := by omega
      simp only [homogeneousCoeffPiece, if_pos hm,
        MvPolynomial.mem_homogeneousSubmodule] at hx
      simp only [homogeneousCoeffPiece, if_pos hn,
        MvPolynomial.mem_homogeneousSubmodule] at hy
      simp only [homogeneousCoeffPiece, if_pos hmn, hnat,
        MvPolynomial.mem_homogeneousSubmodule]
      exact hx.mul hy
    · have hy0 : y = 0 := by simpa [homogeneousCoeffPiece, hn] using hy
      rw [hy0, mul_zero]
      exact (homogeneousCoeffPiece (m + n)).zero_mem
  · have hx0 : x = 0 := by simpa [homogeneousCoeffPiece, hm] using hx
    rw [hx0, zero_mul]
    exact (homogeneousCoeffPiece (m + n)).zero_mem

theorem homogeneousCoeffPiece_C (c : k) :
    MvPolynomial.C c ∈ homogeneousCoeffPiece (σ := σ) 0 := by
  simpa [homogeneousCoeffPiece] using MvPolynomial.isHomogeneous_C σ c

theorem homogeneousCoeffPiece_X (i : σ) :
    MvPolynomial.X i ∈ homogeneousCoeffPiece (k := k) 1 := by
  simpa [homogeneousCoeffPiece] using MvPolynomial.isHomogeneous_X k i

theorem homogeneousCoeffPiece_component (n : ℕ) {m : ℤ} {p : MvPolynomial σ k}
    (hp : p ∈ homogeneousCoeffPiece m) :
    MvPolynomial.homogeneousComponent n p = if (n : ℤ) = m then p else 0 := by
  by_cases hm : 0 ≤ m
  · have hp' : p ∈ MvPolynomial.homogeneousSubmodule σ k m.toNat := by
      simpa [homogeneousCoeffPiece, hm] using hp
    rw [MvPolynomial.homogeneousComponent_of_mem hp']
    have he : n = m.toNat ↔ (n : ℤ) = m := by omega
    simp only [he]
  · have hp0 : p = 0 := by simpa [homogeneousCoeffPiece, hm] using hp
    simp [hp0]

/-- A free generator of weight `w i` contributes coefficient degree `q-w i`.
The resulting subspace is a submodule over `k`, not over `k[σ]`. -/
noncomputable def weightedFreePiece {I : Type*} (w : I → ℕ) (q : ℤ) :
    Submodule k (I →₀ MvPolynomial σ k) where
  carrier := {x | ∀ i, x i ∈ homogeneousCoeffPiece (q - (w i : ℤ))}
  zero_mem' := fun i => (homogeneousCoeffPiece (q - (w i : ℤ))).zero_mem
  add_mem' hx hy := fun i =>
    (homogeneousCoeffPiece (q - (w i : ℤ))).add_mem (hx i) (hy i)
  smul_mem' c _ hx := fun i =>
    (homogeneousCoeffPiece (q - (w i : ℤ))).smul_mem c (hx i)

theorem weightedFreePiece_single {I : Type*} (w : I → ℕ) (q : ℤ)
    (i : I) {r : MvPolynomial σ k}
    (hr : r ∈ homogeneousCoeffPiece (q - (w i : ℤ))) :
    single i r ∈ weightedFreePiece w q := by
  classical
  intro j
  by_cases h : j = i
  · subst j; simpa using hr
  · rw [Finsupp.single_eq_of_ne h]
    exact (homogeneousCoeffPiece (q - (w j : ℤ))).zero_mem

/-- Every shifted free polynomial is a finite sum of homogeneous elements. -/
theorem iSup_weightedFreePiece_nat {I : Type*} (w : I → ℕ) :
    (⨆ n : ℕ, weightedFreePiece (σ := σ) (k := k) w (n : ℤ)) = ⊤ := by
  classical
  apply eq_top_iff.mpr
  intro x _
  rw [← x.sum_single]
  apply Submodule.sum_mem
  intro i _
  rw [(x i).as_sum, Finsupp.single_finsetSum]
  apply Submodule.sum_mem
  intro d _
  apply (le_iSup (fun n : ℕ => weightedFreePiece w (n : ℤ)) (d.degree + w i))
  apply weightedFreePiece_single
  have he : ((d.degree + w i : ℕ) : ℤ) - (w i : ℤ) = (d.degree : ℤ) := by omega
  rw [he, homogeneousCoeffPiece_nat]
  exact MvPolynomial.isHomogeneous_monomial _ rfl

/-- Finite homogeneous sums in a shifted free module are unique. -/
theorem weightedFreePiece_sum_unique {I : Type*} (w : I → ℕ)
    (s : Finset ℕ) (x : ℕ → (I →₀ MvPolynomial σ k))
    (hx : ∀ n ∈ s, x n ∈ weightedFreePiece w (n : ℤ))
    (hs : ∑ n ∈ s, x n = 0) (q : ℕ) (hq : q ∈ s) : x q = 0 := by
  classical
  apply Finsupp.ext
  intro i
  change x q i = 0
  by_cases hqi : w i ≤ q
  · have h := congrArg (fun z => MvPolynomial.homogeneousComponent (q - w i) (z i)) hs
    simp only [Finsupp.finsetSum_apply, Finsupp.zero_apply, map_sum, map_zero] at h
    have hc (n) (hn : n ∈ s) :
        MvPolynomial.homogeneousComponent (q - w i) (x n i) =
          if q = n then x n i else 0 := by
      rw [homogeneousCoeffPiece_component _ (hx n hn i)]
      have he : ((q - w i : ℕ) : ℤ) = (n : ℤ) - w i ↔ q = n := by omega
      simp only [he]
    rw [Finset.sum_congr rfl hc] at h
    simpa [hq] using h
  · have hi := hx q hq i
    rw [homogeneousCoeffPiece_negative (by omega)] at hi
    exact hi

theorem iSupIndep_weightedFreePiece_nat {I : Type*} (w : I → ℕ) :
    iSupIndep (fun n : ℕ => weightedFreePiece (σ := σ) (k := k) w (n : ℤ)) :=
  (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr (weightedFreePiece_sum_unique w)

end Polynomial

end BPFixedPoints.ResolutionTools

namespace BPFixedPoints.ResolutionTools

variable {k R I : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem coefficientwise_smul_constant (P : Submodule k R)
    {r : R} (hr : r ∈ (algebraMap k R).range)
    {x : I →₀ R} (hx : x ∈ coefficientwise P) :
    r • x ∈ coefficientwise P := by
  obtain ⟨c, rfl⟩ := hr
  intro i
  change algebraMap k R c * x i ∈ P
  simpa only [Algebra.smul_def] using P.smul_mem c (hx i)

end BPFixedPoints.ResolutionTools
