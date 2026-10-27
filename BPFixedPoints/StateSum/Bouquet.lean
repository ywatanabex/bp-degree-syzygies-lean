import BPFixedPoints.StateSum.Basic

/-!
# Closed formula for a bouquet of r loops

𝒬_{B_r}(t)=Σ_k C(r,k)φ(2k)t^k=2rt(1+t)^{r−1}−(1+t)^r+2 for r≥1.
At t=1, Q(B_r)=(r−1)2^r+2, also including r=0.
Use `IsBouquetAt`, requiring every edge of A to be a loop at v₀. Other vertices
may be isolated since φ(0)=1.
-/

namespace BPFixedPoints

open Finset Polynomial

/-- Bouquet Q=sum_k choose(r,k) φ(2k). -/
def bouquetQ (r : ℕ) : ℕ := ∑ k ∈ range (r + 1), r.choose k * phi (2 * k)

/-- Bouquet theta(1,2)=sum_k choose(r,k) f_{2k}(2). -/
def bouquetTheta (r : ℕ) : ℕ := ∑ k ∈ range (r + 1), r.choose k * f2 (2 * k)

/-- 2Σ_k k C(r,k) = r 2^r。 -/
theorem two_mul_sum_mul_choose (r : ℕ) :
    2 * ∑ k ∈ range (r + 1), k * r.choose k = r * 2 ^ r := by
  rcases r with _ | n
  · simp
  · rw [Finset.sum_range_succ', zero_mul, add_zero]
    have h : ∀ j, (j + 1) * (n + 1).choose (j + 1) = (n + 1) * n.choose j := fun j => by
      rw [mul_comm, ← Nat.add_one_mul_choose_eq]
    simp_rw [h]
    rw [← Finset.mul_sum, Nat.sum_range_choose]
    ring

/-- Integer bouquet formula (r-1)2^r+2, taking value 1 when r=0. -/
theorem bouquetQ_eq (r : ℕ) : (bouquetQ r : ℤ) = ((r : ℤ) - 1) * 2 ^ r + 2 := by
  have hT := two_mul_sum_mul_choose r
  have hC := Nat.sum_range_choose r
  have key : ∀ k, ((r.choose k * phi (2 * k) : ℕ) : ℤ) =
      2 * ((k * r.choose k : ℕ) : ℤ) - ((r.choose k : ℕ) : ℤ) + (if k = 0 then 2 else 0) := by
    intro k
    rcases k with _ | k
    · simp
    · rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, phi_succ]
      simp only [Nat.succ_ne_zero, ite_false, add_zero]
      push_cast; ring
  unfold bouquetQ
  rw [Nat.cast_sum]
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Nat.cast_sum,
    ← Nat.cast_sum, Finset.sum_ite_eq']
  have hT' : (2 * ((∑ k ∈ range (r + 1), k * r.choose k : ℕ) : ℤ)) = (r : ℤ) * 2 ^ r := by
    exact_mod_cast hT
  have hC' : ((∑ k ∈ range (r + 1), r.choose k : ℕ) : ℤ) = 2 ^ r := by exact_mod_cast hC
  rw [hT', hC']
  simp
  ring

/-- Bouquet polynomial formula 2rt(1+t)^{r-1}-(1+t)^r+2, also valid for r=0. -/
theorem bouquetQpoly_coeff (r k : ℕ) :
    (∑ j ∈ range (r + 1), C ((r.choose j * phi (2 * j) : ℕ) : ℤ) * X ^ j).coeff k =
      ((r.choose k * phi (2 * k) : ℕ) : ℤ) := by
  rw [finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

theorem bouquetQpoly_rhs_coeff_zero (r : ℕ) :
    (C (2 * (r : ℤ)) * X * (1 + X) ^ (r - 1) - (1 + X) ^ r + C 2).coeff 0 = 1 := by
  rw [mul_assoc, coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul_zero, coeff_one_add_X_pow, coeff_C]
  simp

theorem bouquetQpoly_rhs_coeff_succ (r j : ℕ) :
    (C (2 * (r : ℤ)) * X * (1 + X) ^ (r - 1) - (1 + X) ^ r + C 2).coeff (j + 1) =
      2 * (r : ℤ) * ((r - 1).choose j : ℤ) - (r.choose (j + 1) : ℤ) := by
  rw [mul_assoc, coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_one_add_X_pow,
    coeff_one_add_X_pow, coeff_C]
  simp

/-- Bouquet polynomial formula 2rt(1+t)^{r-1}-(1+t)^r+2, also valid for r=0. -/
theorem bouquetQpoly_eq (r : ℕ) :
    (∑ k ∈ range (r + 1), C ((r.choose k * phi (2 * k) : ℕ) : ℤ) * X ^ k) =
      C (2 * (r : ℤ)) * X * (1 + X) ^ (r - 1) - (1 + X) ^ r + C 2 := by
  ext k
  rw [bouquetQpoly_coeff]
  rcases k with _ | j
  · rw [bouquetQpoly_rhs_coeff_zero]; simp
  · rw [bouquetQpoly_rhs_coeff_succ, show 2 * (j + 1) = 2 * j + 1 + 1 by ring, phi_succ]
    rcases r with _ | n
    · simp
    · have h := Nat.add_one_mul_choose_eq n j
      simp only [Nat.add_sub_cancel]
      push_cast
      have h' : ((n : ℤ) + 1) * (n.choose j : ℤ) =
          ((n + 1).choose (j + 1) : ℤ) * ((j : ℤ) + 1) := by exact_mod_cast h
      linear_combination (-2 : ℤ) * h'

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] (G : Multigraph V E)

/-- Every edge in A is a loop at vertex v₀. -/
def IsBouquetAt (A : Finset E) (v₀ : V) : Prop := ∀ e ∈ A, G.fst e = v₀ ∧ G.snd e = v₀

variable {G} {A : Finset E} {v₀ : V} (hB : G.IsBouquetAt A v₀)
include hB

omit [Fintype V] in
theorem deg_of_isBouquetAt {S : Finset E} (hS : S ⊆ A) (w : V) :
    G.deg S w = if w = v₀ then 2 * S.card else 0 := by
  unfold deg
  split_ifs with hw
  · subst hw
    rw [Finset.sum_const_nat (m := 2)]
    · ring
    intro e he
    obtain ⟨h1, h2⟩ := hB e (hS he)
    simp [endCount, h1, h2]
  · apply Finset.sum_eq_zero
    intro e he
    obtain ⟨h1, h2⟩ := hB e (hS he)
    apply G.endCount_of_ne_ne
    · rw [h1]; exact Ne.symm hw
    · rw [h2]; exact Ne.symm hw

theorem wt_of_isBouquetAt (g : ℕ → ℕ) (hg : g 0 = 1) {S : Finset E} (hS : S ⊆ A) :
    G.wt g S = g (2 * S.card) := by
  unfold wt
  rw [Fintype.prod_eq_single v₀]
  · rw [deg_of_isBouquetAt hB hS, if_pos rfl]
  · intro w hw
    rw [deg_of_isBouquetAt hB hS, if_neg hw, hg]

theorem QOn_of_isBouquetAt : G.QOn A = bouquetQ A.card := by
  unfold QOn bouquetQ
  rw [Finset.sum_congr rfl fun S hS => wt_of_isBouquetAt hB phi rfl (Finset.mem_powerset.1 hS),
    Finset.sum_powerset_apply_card (fun k => phi (2 * k))]
  simp [smul_eq_mul]

theorem thetaOn_of_isBouquetAt : G.thetaOn A = bouquetTheta A.card := by
  unfold thetaOn bouquetTheta
  rw [Finset.sum_congr rfl fun S hS => wt_of_isBouquetAt hB f2 rfl (Finset.mem_powerset.1 hS),
    Finset.sum_powerset_apply_card (fun k => f2 (2 * k))]
  simp [smul_eq_mul]

theorem QpolyOn_of_isBouquetAt :
    G.QpolyOn A = C (2 * (A.card : ℤ)) * X * (1 + X) ^ (A.card - 1) - (1 + X) ^ A.card + C 2 := by
  rw [← bouquetQpoly_eq]
  unfold QpolyOn
  rw [Finset.sum_congr rfl fun S hS => by
      rw [wt_of_isBouquetAt hB phi rfl (Finset.mem_powerset.1 hS)],
    Finset.sum_powerset_apply_card (fun k => (X : ℤ[X]) ^ k * (phi (2 * k) : ℤ[X]))]
  apply Finset.sum_congr rfl
  intro k _
  rw [nsmul_eq_mul, Nat.cast_mul, Polynomial.C_mul, ← Polynomial.C_eq_natCast,
    ← Polynomial.C_eq_natCast]
  ring

end Multigraph

end BPFixedPoints
