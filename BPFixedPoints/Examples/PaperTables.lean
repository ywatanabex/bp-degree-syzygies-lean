import BPFixedPoints.Incidence.Generators
import BPFixedPoints.Incidence.Omega
import BPFixedPoints.Examples.K4Omega
import BPFixedPoints.Degree.GenericDegree
import BPFixedPoints.Real.SectorBounds

/-!
# Paper table and K₄ example

* The §3 table following `alg:generator-real-bridge` gives
  (Q(G),Σ_q β_{0,q},2^ν)=(2,2,2) for the triangle, (48,8,8) for K₄ and (6,3,4)
  for the bowtie (`table_triangle`, `table_K4`, `table_bowtie`). Its two-triangle
  union is Eulerian with one degree-four vertex, weight three and homological
  degree one (`bowtie_union`).
* `alg:k4-section` and `fig:k4-states`: `K4_state_counts` gives the types,
  counts, weights and degrees; `K4_betti_rows` gives (8,24,16). `K4_omegaTilde`
  and `K4_omegaTilde_eval_one` give ω̃=ω and length 30, while total Betti number
  is 48. Generator states are empty, four triangles and three squares; any two
  nonempty ones meet at a vertex (`K4_cycleUnions_meet`).
* Supplement `sf:k4-states`: at strong fields the complex/real/positive counts
  are (48,8,1). There is one real root per Eulerian state (empty, triangle,
  square), by `K4_strong_field` and `K4_sector_strong_field`.

All finite counts use kernel-checked `decide`.
-/

set_option maxRecDepth 20000

namespace BPFixedPoints.Examples

open Multigraph Polynomial

/-! ### Eulerian edge sets and ν -/

theorem triangle_evenSets : (Finset.univ.filter triangle.IsEvenSet).card = 2 := by decide
theorem K4_evenSets : (Finset.univ.filter K4.IsEvenSet).card = 8 := by decide
theorem bowtie_evenSets : (Finset.univ.filter bowtie.IsEvenSet).card = 4 := by decide

theorem nu_eq_of_card_evenSets {V E : Type*} [DecidableEq V] [Fintype V] [DecidableEq E]
    [Fintype E] (G : Multigraph V E) {k : ℕ} (h : (Finset.univ.filter G.IsEvenSet).card = 2 ^ k) :
    G.nu = k := by
  rw [card_evenSets_eq_two_pow_nu] at h
  exact Nat.pow_right_injective le_rfl h

theorem triangle_nu : triangle.nu = 1 := nu_eq_of_card_evenSets _ triangle_evenSets
theorem K4_nu : K4.nu = 3 := nu_eq_of_card_evenSets _ K4_evenSets
theorem bowtie_nu : bowtie.nu = 2 := nu_eq_of_card_evenSets _ bowtie_evenSets

/-! ### Generators: unions of cycles -/

theorem triangle_cycleUnions : (Finset.univ.filter triangle.IsCycleUnion).card = 2 := by decide
theorem K4_cycleUnions : (Finset.univ.filter K4.IsCycleUnion).card = 8 := by decide
theorem bowtie_cycleUnions : (Finset.univ.filter bowtie.IsCycleUnion).card = 3 := by decide

/-- **§3 table, triangle:** (Q,Σ_q β_{0,q},2^ν)=(2,2,2). -/
theorem table_triangle :
    (triangle.Q, ∑ q ∈ Finset.range (Fintype.card (Fin 3) + 1), triangle.betti 0 q,
      2 ^ triangle.nu) = (2, 2, 2) := by
  rw [sum_betti_zero_eq_card, triangle_cycleUnions, triangle_nu, triangle_Q]; rfl

/-- **§3 table, K₄:** (Q,Σ_q β_{0,q},2^ν)=(48,8,8). -/
theorem table_K4 :
    (K4.Q, ∑ q ∈ Finset.range (Fintype.card (Fin 6) + 1), K4.betti 0 q, 2 ^ K4.nu) =
      (48, 8, 8) := by
  rw [sum_betti_zero_eq_card, K4_cycleUnions, K4_nu, K4_Q]; rfl

/-- **§3 table, bowtie (two triangles sharing a vertex):** (Q,Σ_q β_{0,q},2^ν)=(6,3,4). -/
theorem table_bowtie :
    (bowtie.Q, ∑ q ∈ Finset.range (Fintype.card (Fin 6) + 1), bowtie.betti 0 q,
      2 ^ bowtie.nu) = (6, 3, 4) := by
  rw [sum_betti_zero_eq_card, bowtie_cycleUnions, bowtie_nu, bowtie_Q]; rfl

/-- The full bowtie edge set is Eulerian, has degree four at vertex 0, weight three and homological degree |S|−v(S)=1. It gives a real sector but is not a generator. -/
theorem bowtie_union :
    bowtie.IsEvenSet Finset.univ ∧ bowtie.deg Finset.univ 0 = 4 ∧
      bowtie.wt phi Finset.univ = 3 ∧
      (Finset.univ : Finset (Fin 6)).card - (bowtie.support Finset.univ).card = 1 := by
  decide

/-- The bowtie's two edge-disjoint simple cycles (triangles) meet at vertex 0. -/
theorem bowtie_not_eq : ∑ q ∈ Finset.range (Fintype.card (Fin 6) + 1), bowtie.betti 0 q ≠
    2 ^ bowtie.nu := by
  rw [sum_betti_zero_eq_card, bowtie_cycleUnions, bowtie_nu]; decide

/-! ### K₄ state classification (`fig:k4-states`) -/

/-- For each edge count q, give the number of contributing states, their total weight, and the set of homological degrees p=q−v(S). The types for q=0,3,4,5,6 are empty, triangles, squares, K₄−e and K₄. -/
theorem K4_state_counts :
    ((List.range 7).map fun q =>
      ((Finset.univ.filter fun S : Finset (Fin 6) => K4.IsContributing S ∧ S.card = q).card,
       ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin 6) => K4.IsContributing S ∧ S.card = q),
         K4.wt phi S,
       (Finset.univ.filter (fun S : Finset (Fin 6) => K4.IsContributing S ∧ S.card = q)).image
         fun S => S.card - (K4.support S).card)) =
      [(1, 1, {0}), (0, 0, ∅), (0, 0, ∅), (4, 4, {0}), (3, 3, {0}), (6, 24, {1}), (1, 16, {2})] := by
  decide

/-- Eulerian states of K₄ are exactly the empty, triangle and square contributing states (edge counts 0,3,4). -/
theorem K4_isEvenSet_iff (S : Finset (Fin 6)) :
    K4.IsEvenSet S ↔ K4.IsContributing S ∧ (S.card = 0 ∨ S.card = 3 ∨ S.card = 4) := by
  revert S; decide

/-- K₄ generator states (cycle unions) are precisely its Eulerian states; any two nonempty ones share a vertex, so all products of nonunit generators in the cycle compatibility algebra vanish. -/
theorem K4_cycleUnions_meet :
    (∀ S : Finset (Fin 6), K4.IsCycleUnion S ↔ K4.IsEvenSet S) ∧
      ∀ C D : Finset (Fin 6), K4.IsCycleUnion C → K4.IsCycleUnion D → C.Nonempty →
        D.Nonempty → ¬ Disjoint (K4.support C) (K4.support D) := by
  decide

/-! ### K₄: ω and Artin length -/

/-- Contributing K₄ states satisfy |S|−v(S)≤2. -/
theorem K4_card_le (S : Finset (Fin 6)) (hS : K4.IsContributing S) :
    S.card ≤ (K4.support S).card + 2 := by
  revert S; decide

/-- K₄ has no tree component (τ=0). The maximal |S|−v(S) among contributing states is ρ=m−n+τ=2. -/
theorem K4_tau : K4.tau = 0 := by
  have h1 := K4.rho_add_card
  obtain ⟨S, hSc, hS⟩ := K4.exists_isContributing_card_eq
  have h2 := K4_card_le S hSc
  simp only [Fintype.card_fin] at h1
  omega

theorem K4_rho : K4.rho = 2 := by
  have := K4.rho_add_card
  rw [K4_tau] at this
  simpa using this

/-- **For K₄, ω̃=ω=1+2t+3t²+8t³+16t⁴**, since it has no tree component. -/
theorem K4_omegaTilde : K4.omegaTilde = 1 + 2 * X + 3 * X ^ 2 + 8 * X ^ 3 + 16 * X ^ 4 := by
  symm
  refine K4.omegaTilde_unique ?_
  rw [K4_rho, K4_thetaTwoI]

theorem K4_omega : K4.omega = 1 + 2 * X + 3 * X ^ 2 + 8 * X ^ 3 + 16 * X ^ 4 := by
  rw [omega_eq_omegaTilde_of_tau_eq_zero _ K4_tau, K4_omegaTilde]

/-- **Artin length ω̃(1)=30**, while total Betti number is 48. -/
theorem K4_omegaTilde_eval_one : K4.omegaTilde.eval 1 = 30 := by
  rw [K4_omegaTilde]; norm_num

/-- For K₄, d_G=3m+n−τ=22. -/
theorem K4_dG : K4.dG = 22 := by
  rw [dG, K4_tau]; simp

/-! ### K₄ at strong fields (`sf:k4-states`) -/

theorem K4_loopless : K4.Loopless := by unfold Multigraph.Loopless; decide

/-- **Strong-field K₄ counts (48,8,1).** For fixed a_e>0, a_e≠1 and all |log b_i| sufficiently large, there are 48 simple admissible complex solutions, eight real ones and one with all messages positive. -/
theorem K4_strong_field {a : Fin 6 → ℝ} (ha : ∀ e, 0 < a e) (ha1 : ∀ e, a e ≠ 1) :
    ∃ H : ℝ, ∀ b : Fin 4 → ℝ, (∀ i, 0 < b i) → (∀ i, H ≤ |Real.log (b i)|) →
      Nat.card {y : BP.Dart (Fin 6) → ℂ //
          K4.IsAdmissibleSolution (fun e => (a e : ℂ)) (fun i => (b i : ℂ)) y} = 48 ∧
      (∀ y, K4.IsAdmissibleSolution (fun e => (a e : ℂ)) (fun i => (b i : ℂ)) y →
        K4.IsSimpleSolution (fun e => (a e : ℂ)) (fun i => (b i : ℂ)) y) ∧
      Nat.card {y : BP.Dart (Fin 6) → ℝ // K4.IsAdmissibleSolution a b y} = 8 ∧
      Nat.card {y : BP.Dart (Fin 6) → ℝ // K4.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} = 1 := by
  obtain ⟨H, hH⟩ := K4.strong_field_three_counts K4_loopless ha ha1
  refine ⟨H, fun b hb hbH => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hH b hb hbH
  rw [K4_Q] at h1
  rw [K4_evenSets] at h3
  exact ⟨h1, h2, h3, h4⟩

/-- At strong fields K₄ has one real root in each Eulerian state (empty, four triangles, three squares), and none in K₄−e or K₄ states, as in the last row of `fig:k4-states`. -/
theorem K4_sector_strong_field {a : Fin 6 → ℝ} (ha : ∀ e, 0 < a e) (ha1 : ∀ e, a e ≠ 1) :
    ∃ H : ℝ, ∀ b : Fin 4 → ℝ, (∀ i, 0 < b i) → (∀ i, H ≤ |Real.log (b i)|) →
      ∀ S : Finset (Fin 6),
        Nat.card {y : BP.Dart (Fin 6) → ℝ // K4.IsAdmissibleSolution a b y ∧ BP.negSupport y = S} =
          if K4.IsContributing S ∧ (S.card = 0 ∨ S.card = 3 ∨ S.card = 4) then 1 else 0 := by
  obtain ⟨H, hH⟩ := card_sector_strong_field ha ha1 K4_loopless
  refine ⟨H, fun b hb hbH S => ?_⟩
  rw [hH b hb hbH S]
  simp only [K4_isEvenSet_iff]

end BPFixedPoints.Examples
