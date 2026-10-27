import BPFixedPoints.StateSum.Bouquet
import BPFixedPoints.StateSum.DeletionContraction

/-!
# Comparing θ(·,2) with Q, the 2-core and the bouquet recurrence

`QpolyOn_coeff_le` gives coefficientwise 𝒬_A≤θ_A(·,2) from φ(d)≤f_d(2),
hence Q≤θ(1,2) (`QOn_le_thetaOn`). `thetaOn_eq_QOn_iff` characterizes equality
by maximum degree at most three in the 2-core; under this condition the entire
polynomials agree (`thetaPolyOn_eq_QpolyOn_of_core`).
A generalized loop `IsGenLoop` has no degree-one vertex; degree-zero vertices
are allowed. These are the only possibly contributing sets. Define `core A`
as the union of all generalized loops contained in A, mathematically equivalent
to repeated removal of vertices of degree at most one. The equivalence is not
proved in this file. The definition gives `core_subset`, `isGenLoop_core`
(using union closure `isGenLoop_union`) and `subset_core`, enough for equality.

The bouquet special value Σ_k C(r,k)f_{2k}(2) (`bouquetTheta`) equals the integer
sequence U₀=1,U₁=2,U_{n+2}=8U_{n+1}−8U_n (`bouquetTheta_eq_U`). Its characteristic
roots are 4±2√2, yielding the stated closed form, proved elsewhere. Here use
a_k=f_{2k}(2), a_{k+2}=6a_{k+1}−a_k (`f2Even_add_two`), and its binomial
transform b_{n+1}=b_n+Σ_k C(n,k)a_{k+1} (`binom_succ`,
`Finset.sum_choose_succ_mul`).
-/

namespace BPFixedPoints

open Finset Polynomial

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] (G : Multigraph V E)

section Compare

/-- Each coefficient of 𝒬_A(t) is bounded by the matching coefficient of θ_A(t,2). -/
theorem QpolyOn_coeff_le (A : Finset E) (k : ℕ) :
    (G.QpolyOn A).coeff k ≤ (G.thetaPolyOn A).coeff k := by
  unfold QpolyOn thetaPolyOn
  rw [finsetSum_coeff, finsetSum_coeff]
  apply Finset.sum_le_sum
  intro S _
  rw [coeff_X_pow_mul', coeff_X_pow_mul', coeff_natCast_ite, coeff_natCast_ite]
  split_ifs
  · exact_mod_cast G.wt_phi_le_wt_f2 S
  · exact le_rfl
  · exact le_rfl

/-- Q ≤ θ(1,2)（t=1）。 -/
theorem QOn_le_thetaOn (A : Finset E) : G.QOn A ≤ G.thetaOn A :=
  Finset.sum_le_sum fun S _ => G.wt_phi_le_wt_f2 S

end Compare

section GenLoop

/-- Generalized loop: an edge set with no degree-one vertex, allowing isolated vertices. Only such sets can contribute to Q or θ. -/
def IsGenLoop (S : Finset E) : Prop := ∀ v, G.deg S v ≠ 1

instance (S : Finset E) : Decidable (G.IsGenLoop S) := by
  unfold IsGenLoop; infer_instance

omit [Fintype V] in
theorem isGenLoop_empty : G.IsGenLoop ∅ := fun v => by simp

omit [Fintype V] in
/-- A union of generalized loops is a generalized loop. -/
theorem isGenLoop_union [DecidableEq E] {S T : Finset E} (hS : G.IsGenLoop S)
    (hT : G.IsGenLoop T) : G.IsGenLoop (S ∪ T) := by
  intro v
  have h1 : G.deg S v ≤ G.deg (S ∪ T) v := G.deg_mono Finset.subset_union_left v
  have h2 : G.deg T v ≤ G.deg (S ∪ T) v := G.deg_mono Finset.subset_union_right v
  have hS' := hS v
  have hT' := hT v
  by_cases h0 : G.deg S v = 0 ∧ G.deg T v = 0
  · obtain ⟨h0S, h0T⟩ := h0
    have : G.deg (S ∪ T) v = 0 := by
      rw [deg_eq_zero_iff] at h0S h0T ⊢
      intro e he
      rcases Finset.mem_union.1 he with he | he
      · exact h0S e he
      · exact h0T e he
    omega
  · omega

omit [Fintype V] in
/-- A set that is not a generalized loop has a degree-one vertex. -/
theorem exists_deg_eq_one_of_not_isGenLoop {S : Finset E} (h : ¬ G.IsGenLoop S) :
    ∃ v, G.deg S v = 1 := by
  unfold IsGenLoop at h
  obtain ⟨v, hv⟩ := not_forall.1 h
  exact ⟨v, not_ne_iff.1 hv⟩

variable [DecidableEq E]

/-- 2-core of A: union of all generalized loops in A. Agreement with iterative removal of vertices of degree at most one is `isPruned_iff` in `TwoCore.lean`. -/
def core (A : Finset E) : Finset E := (A.powerset.filter G.IsGenLoop).sup id

theorem core_subset (A : Finset E) : G.core A ⊆ A :=
  Finset.sup_le fun _ hS => Finset.mem_powerset.1 (Finset.mem_filter.1 hS).1

/-- The 2-core is a generalized loop. -/
theorem isGenLoop_core (A : Finset E) : G.IsGenLoop (G.core A) := by
  unfold core
  refine Finset.sup_induction G.isGenLoop_empty ?_ ?_
  · intro S hS T hT
    exact G.isGenLoop_union hS hT
  · intro S hS
    exact (Finset.mem_filter.1 hS).2

/-- Every generalized loop in A lies in its 2-core. -/
theorem subset_core {S A : Finset E} (hS : S ⊆ A) (h : G.IsGenLoop S) : S ⊆ G.core A :=
  Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hS, h⟩)

end GenLoop

section Equality

variable [DecidableEq E]

/-- If the 2-core is subcubic, f₂ and φ weights agree on every subset of A. -/
theorem wt_f2_eq_wt_phi_of_core {A : Finset E} (h : ∀ v, G.deg (G.core A) v ≤ 3)
    {S : Finset E} (hS : S ⊆ A) : G.wt f2 S = G.wt phi S := by
  by_cases hgl : G.IsGenLoop S
  · have hsub := G.subset_core hS hgl
    unfold wt
    apply Finset.prod_congr rfl
    intro v _
    exact f2_eq_phi_of_le_three ((G.deg_mono hsub v).trans (h v))
  · obtain ⟨v, hv⟩ := G.exists_deg_eq_one_of_not_isGenLoop hgl
    rw [G.wt_f2_eq_zero_of_deg_eq_one hv, G.wt_phi_eq_zero_of_deg_eq_one hv]

/-- A subcubic 2-core gives θ_A(t,2)=𝒬_A(t) termwise. -/
theorem thetaPolyOn_eq_QpolyOn_of_core (A : Finset E) (h : ∀ v, G.deg (G.core A) v ≤ 3) :
    G.thetaPolyOn A = G.QpolyOn A := by
  unfold thetaPolyOn QpolyOn
  apply Finset.sum_congr rfl
  intro S hS
  rw [G.wt_f2_eq_wt_phi_of_core h (Finset.mem_powerset.1 hS)]

/-- A subcubic 2-core gives θ(1,2)=Q. -/
theorem thetaOn_eq_QOn_of_core (A : Finset E) (h : ∀ v, G.deg (G.core A) v ≤ 3) :
    G.thetaOn A = G.QOn A := by
  unfold thetaOn QOn
  apply Finset.sum_congr rfl
  intro S hS
  exact G.wt_f2_eq_wt_phi_of_core h (Finset.mem_powerset.1 hS)

/-- A degree-at-least-four vertex in the 2-core gives Q<θ(1,2): the core term is strictly smaller for φ than f₂, and all others are weakly smaller. -/
theorem QOn_lt_thetaOn_of_four_le {A : Finset E} {v₀ : V} (h : 4 ≤ G.deg (G.core A) v₀) :
    G.QOn A < G.thetaOn A := by
  unfold QOn thetaOn
  apply Finset.sum_lt_sum
  · intro S _
    exact G.wt_phi_le_wt_f2 S
  · refine ⟨G.core A, Finset.mem_powerset.2 (G.core_subset A), ?_⟩
    show G.wt phi (G.core A) < G.wt f2 (G.core A)
    unfold wt
    apply Finset.prod_lt_prod₀
    · intro v _
      exact phi_pos_of_ne_one (G.isGenLoop_core A v)
    · intro v _
      exact phi_le_f2 _
    · exact ⟨v₀, Finset.mem_univ v₀, phi_lt_f2_of_four_le h⟩

/-- θ(1,2)=Q iff every 2-core vertex has degree at most three. -/
theorem thetaOn_eq_QOn_iff (A : Finset E) :
    G.thetaOn A = G.QOn A ↔ ∀ v, G.deg (G.core A) v ≤ 3 := by
  constructor
  · intro heq
    by_contra hne
    obtain ⟨v₀, hv₀⟩ := not_forall.1 hne
    have h4 : 4 ≤ G.deg (G.core A) v₀ := by omega
    exact absurd heq (G.QOn_lt_thetaOn_of_four_le h4).ne'
  · exact G.thetaOn_eq_QOn_of_core A

end Equality

end Multigraph

section BouquetTheta

/-- U₀=1,U₁=2,U_{n+2}=8U_{n+1}−8U_n. Characteristic roots 4±2√2 give U_ν=(4+2√2)^{ν−1}+(4−2√2)^{ν−1}. -/
def U : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 8 * U (n + 1) - 8 * U n

@[simp] theorem U_zero : U 0 = 1 := rfl
@[simp] theorem U_one : U 1 = 2 := rfl
theorem U_add_two (n : ℕ) : U (n + 2) = 8 * U (n + 1) - 8 * U n := rfl
theorem U_two : U 2 = 8 := by decide
theorem U_three : U 3 = 48 := by decide

/-- a_k=f_{2k}(2), regarded as an integer. -/
def f2Even (k : ℕ) : ℤ := (f2 (2 * k) : ℤ)

@[simp] theorem f2Even_zero : f2Even 0 = 1 := by simp [f2Even]
@[simp] theorem f2Even_one : f2Even 1 = 1 := by simp [f2Even, f2_two]

/-- a_{k+2}=6a_{k+1}−a_k, eliminating odd terms from the f₂ recurrence. -/
theorem f2Even_add_two (k : ℕ) : f2Even (k + 2) = 6 * f2Even (k + 1) - f2Even k := by
  unfold f2Even
  have h1 : f2 (2 * k + 4) = 2 * f2 (2 * k + 3) + f2 (2 * k + 2) := f2_add_two (2 * k + 2)
  have h2 : f2 (2 * k + 3) = 2 * f2 (2 * k + 2) + f2 (2 * k + 1) := f2_add_two (2 * k + 1)
  have h3 : f2 (2 * k + 2) = 2 * f2 (2 * k + 1) + f2 (2 * k) := f2_add_two (2 * k)
  rw [show 2 * (k + 2) = 2 * k + 4 by ring, show 2 * (k + 1) = 2 * k + 2 by ring]
  omega

/-- Binomial transform Σ_{k≤n}C(n,k)a_k. -/
def binom (a : ℕ → ℤ) (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), (n.choose k : ℤ) * a k

@[simp] theorem binom_zero (a : ℕ → ℤ) : binom a 0 = a 0 := by simp [binom]

/-- Pascal identity b_{n+1}=b_n+Σ_k C(n,k)a_{k+1}. -/
theorem binom_succ (a : ℕ → ℤ) (n : ℕ) :
    binom a (n + 1) = binom a n + binom (fun k => a (k + 1)) n := by
  unfold binom
  exact Finset.sum_choose_succ_mul (fun i _ => a i) n

theorem binom_sub (a b : ℕ → ℤ) (n : ℕ) :
    binom (fun k => a k - b k) n = binom a n - binom b n := by
  simp only [binom, mul_sub, Finset.sum_sub_distrib]

theorem binom_const_mul (c : ℤ) (a : ℕ → ℤ) (n : ℕ) :
    binom (fun k => c * a k) n = c * binom a n := by
  simp only [binom, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem binom_f2Even_shift_two (n : ℕ) :
    binom (fun k => f2Even (k + 2)) n =
      6 * binom (fun k => f2Even (k + 1)) n - binom f2Even n := by
  have hfun : (fun k => f2Even (k + 2)) = fun k => 6 * f2Even (k + 1) - f2Even k := by
    funext k; exact f2Even_add_two k
  rw [hfun, binom_sub, binom_const_mul]

/-- The transform b_n=Σ_k C(n,k)a_k satisfies b_{n+2}=8b_{n+1}−8b_n. -/
theorem binom_f2Even_add_two (n : ℕ) :
    binom f2Even (n + 2) = 8 * binom f2Even (n + 1) - 8 * binom f2Even n := by
  have h1 := binom_succ f2Even n
  have h2 := binom_succ f2Even (n + 1)
  have h3 : binom (fun k => f2Even (k + 1)) (n + 1) =
      binom (fun k => f2Even (k + 1)) n + binom (fun k => f2Even (k + 2)) n :=
    binom_succ (fun k => f2Even (k + 1)) n
  have h4 := binom_f2Even_shift_two n
  linear_combination h2 + h3 + h4 - 7 * h1

theorem binom_f2Even_eq_U (n : ℕ) : binom f2Even n = U n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    have h := binom_succ f2Even 0
    rw [zero_add] at h
    rw [h, binom_zero, binom_zero, f2Even_zero, f2Even_one, U_one]
    norm_num
  | more n ih0 ih1 => rw [binom_f2Even_add_two, ih0, ih1, U_add_two]

/-- The bouquet value θ_{B_r}(1,2)=Σ_k C(r,k)f_{2k}(2) equals U_r. -/
theorem bouquetTheta_eq_U (r : ℕ) : (bouquetTheta r : ℤ) = U r := by
  rw [← binom_f2Even_eq_U]
  simp [bouquetTheta, binom, f2Even]

end BouquetTheta

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [Fintype V] {G : Multigraph V E} {A : Finset E} {v₀ : V}

/-- If A is a bouquet at v₀, θ(1,2)=U_{|A|}. -/
theorem thetaOn_of_isBouquetAt_eq_U (hB : G.IsBouquetAt A v₀) :
    (G.thetaOn A : ℤ) = U A.card := by
  rw [thetaOn_of_isBouquetAt hB, bouquetTheta_eq_U]

end Multigraph

end BPFixedPoints
