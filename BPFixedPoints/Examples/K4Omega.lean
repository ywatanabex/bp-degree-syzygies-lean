import BPFixedPoints.Incidence.Betti
import BPFixedPoints.Examples.Graphs

/-!
# First-page Betti examples: K₄ in the introduction

The homological row sums for K₄ are (8,24,16), totaling 48=N(K₄).
Entries: β_{0,0}=1 (empty), β_{0,3}=4 (triangles), β_{0,4}=3 (squares),
β_{1,5}=24 (six theta subgraphs, each weight 2·2), β_{2,6}=16 (K₄, weight 2⁴).
The alternating sum 8−24+16=0 agrees with ν=3≥2 (`thetaTwoI_eval_one_eq_zero`).
All computations use kernel-checked `decide`.
-/

namespace BPFixedPoints.Examples

open Multigraph

theorem K4_betti_rows :
    (∑ k ∈ Finset.range 7, K4.betti 0 k, ∑ k ∈ Finset.range 7, K4.betti 1 k,
      ∑ k ∈ Finset.range 7, K4.betti 2 k) = (8, 24, 16) := by
  decide

theorem K4_betti_entries :
    (K4.betti 0 0, K4.betti 0 3, K4.betti 0 4, K4.betti 1 5, K4.betti 2 6) = (1, 4, 3, 24, 16) := by
  decide

end BPFixedPoints.Examples

/-! ## Examples of ω_G: K₄ and three parallel edges P₃ -/

namespace BPFixedPoints.Examples

open Multigraph Polynomial

/-- Coefficients of the polynomial Σ_{k<n}c_k t^k. -/
theorem coeff_sum_range (n : ℕ) (c : ℕ → ℤ) (k : ℕ) :
    (∑ j ∈ Finset.range n, C (c j) * X ^ j : ℤ[X]).coeff k = if k < n then c k else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

/-- Coefficients of θ_{K₄}(t,2i): 1+4t³+3t⁴−24t⁵+16t⁶. -/
def K4thetaCoeff (k : ℕ) : ℤ :=
  if k = 0 then 1 else if k = 3 then 4 else if k = 4 then 3 else if k = 5 then -24
  else if k = 6 then 16 else 0

theorem K4_thetaTwoI_coeff (k : ℕ) : K4.thetaTwoI.coeff k = K4thetaCoeff k := by
  rw [coeff_thetaTwoI]
  by_cases hk : k < 7
  · have h : ∀ j : Fin 7, (-1 : ℤ) ^ (j : ℕ) *
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 6) => S.card = (j : ℕ)),
          ∏ v, (1 - (K4.deg S v : ℤ)) = K4thetaCoeff j := by decide
    exact h ⟨k, hk⟩
  · have hempty : Finset.univ.filter (fun S : Finset (Fin 6) => S.card = k) = ∅ := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h
      have := S.card_le_univ
      simp only [Fintype.card_fin] at this
      omega
    rw [hempty, Finset.sum_empty, mul_zero, K4thetaCoeff]
    split_ifs <;> omega

/-- **K₄:** θ(t,2i)=(1−t)²ω(t), with ω(t)=1+2t+3t²+8t³+16t⁴ and ω(1)=30 (paper introduction). -/
theorem K4_thetaTwoI :
    K4.thetaTwoI = (1 - X) ^ 2 * (1 + 2 * X + 3 * X ^ 2 + 8 * X ^ 3 + 16 * X ^ 4) := by
  have h : K4.thetaTwoI = ∑ j ∈ Finset.range 7, C (K4thetaCoeff j) * X ^ j := by
    ext k
    rw [K4_thetaTwoI_coeff, coeff_sum_range]
    split_ifs with hk
    · rfl
    · simp only [K4thetaCoeff]; split_ifs <;> omega
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, K4thetaCoeff]
  simp
  ring

theorem K4_omega_one :
    (1 + 2 * X + 3 * X ^ 2 + 8 * X ^ 3 + 16 * X ^ 4 : ℤ[X]).eval 1 = 30 := by norm_num

/-- Three parallel edges P₃ (ν=2). -/
def parallel3 : Multigraph (Fin 2) (Fin 3) where
  fst := ![0, 0, 0]
  snd := ![1, 1, 1]

def P3thetaCoeff (k : ℕ) : ℤ := if k = 0 then 1 else if k = 2 then 3 else if k = 3 then -4 else 0

theorem P3_thetaTwoI_coeff (k : ℕ) : parallel3.thetaTwoI.coeff k = P3thetaCoeff k := by
  rw [coeff_thetaTwoI]
  by_cases hk : k < 4
  · have h : ∀ j : Fin 4, (-1 : ℤ) ^ (j : ℕ) *
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 3) => S.card = (j : ℕ)),
          ∏ v, (1 - (parallel3.deg S v : ℤ)) = P3thetaCoeff j := by decide
    exact h ⟨k, hk⟩
  · have hempty : Finset.univ.filter (fun S : Finset (Fin 3) => S.card = k) = ∅ := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h
      have := S.card_le_univ
      simp only [Fintype.card_fin] at this
      omega
    rw [hempty, Finset.sum_empty, mul_zero, P3thetaCoeff]
    split_ifs <;> omega

/-- **P₃:** θ(t,2i)=(1−t)(1+t+4t²), ω(1)=6, different from generic BP degree N=8. -/
theorem P3_thetaTwoI : parallel3.thetaTwoI = (1 - X) * (1 + X + 4 * X ^ 2) := by
  have h : parallel3.thetaTwoI = ∑ j ∈ Finset.range 4, C (P3thetaCoeff j) * X ^ j := by
    ext k
    rw [P3_thetaTwoI_coeff, coeff_sum_range]
    split_ifs with hk
    · rfl
    · simp only [P3thetaCoeff]; split_ifs <;> omega
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, P3thetaCoeff]
  simp
  ring

theorem P3_Q : parallel3.Q = 8 := by decide

end BPFixedPoints.Examples
