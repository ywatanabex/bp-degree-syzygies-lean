import BPFixedPoints.StrongField.StatewiseChartCounts
import BPFixedPoints.Examples.PaperTables

/-!
# Statewise chart counts of K₄ (`fig:k4-states`, `sf:k4-states`, `real:all-real-states`)

Instances of `StrongField/StatewiseChartCounts.lean` for K₄.

* `K4_state_wt`, `K4_state_isEvenSet_iff`, `K4_isEvenSet_iff_isState` and `K4_state_type_table`
  (kernel-checked `decide`): the contributing states of K₄ are the empty set (q=0), four triangles
  (q=3), three four-cycles (q=4), six copies of K₄−e (q=5) and K₄ (q=6), with weights 1, 1, 1, 4
  and 16; exactly the first three types are Eulerian.
* `K4_statewise_chart_counts`: for a_e≠0, a_e²≠1 and all sufficiently small nonzero p, the chart
  of each state contributes wt(S) complex solutions (16, 4 or 1), the per-type totals are the
  complex row 1, 4, 3, 24, 16 of `fig:k4-states`, and the charts partition the 48 solutions.
* `K4_statewise_real_chart_counts`: for real a_e>0, a_e≠1 and all sufficiently small real p>0,
  with positive real root tuples, the chart of each Eulerian state contains exactly one real
  solution and the charts of K₄−e and K₄ none; the per-type real totals are the row 1, 4, 3, 0, 0
  of `fig:k4-states`; the eight real solutions are exactly the real chart solutions of the
  Eulerian states, and the real root of the chart of S has negative messages exactly on the
  edges of S, so it is positive only for S=∅ (`sf:k4-states`).

The orthant is the positive one (small p_i>0); other orthants follow from
`exists_statewise_real_chart_counts_of_orthant`, which is not instantiated here.
-/

set_option maxRecDepth 20000

namespace BPFixedPoints.Examples

open Multigraph

/-- Weights of the K₄ states: 16 for K₄, 4 for K₄−e and 1 for the empty set, the triangles and
the four-cycles. -/
theorem K4_state_wt (S : Finset (Fin 6)) (hS : IsState K4 S) :
    K4.wt phi S = if S.card = 6 then 16 else if S.card = 5 then 4 else 1 := by
  revert S; decide

/-- A K₄ state is Eulerian iff it has at most four edges (empty, triangle, four-cycle). -/
theorem K4_state_isEvenSet_iff (S : Finset (Fin 6)) (hS : IsState K4 S) :
    K4.IsEvenSet S ↔ S.card ≤ 4 := by
  revert S; decide

/-- A K₄ edge set is Eulerian iff it is a state with at most four edges. -/
theorem K4_isEvenSet_iff_isState (S : Finset (Fin 6)) :
    K4.IsEvenSet S ↔ IsState K4 S ∧ S.card ≤ 4 := by
  revert S; decide

/-- **The state types of K₄ (`fig:k4-states`).** For each edge count q: the number of states, the
sum of their weights, and the number of Eulerian ones. -/
theorem K4_state_type_table :
    (List.range 7).map (fun q =>
      (((Finset.univ.filter fun S : Finset (Fin 6) => S.card = q).filter (IsState K4)).card,
       ∑ S ∈ (Finset.univ.filter fun S : Finset (Fin 6) => S.card = q).filter (IsState K4),
         K4.wt phi S,
       ((Finset.univ.filter fun S : Finset (Fin 6) => S.card = q).filter K4.IsEvenSet).card)) =
      [(1, 1, 1), (0, 0, 0), (0, 0, 0), (4, 4, 4), (3, 3, 3), (6, 24, 0), (1, 16, 0)] := by
  decide

/-- **Statewise complex chart counts of K₄ (`fig:k4-states`, `sf:k4-states`).** For fixed
a_e≠0 with a_e²≠1 there are power-map charts, one for each state, such that for all sufficiently
small nonzero p, at b=p⁻¹: the chart of a state contributes 16 solutions for K₄, 4 for each
K₄−e and 1 for the empty set, each triangle and each four-cycle; by edge count q=0,…,6 the
numbers of states and of chart solutions are those of the table (1,4,3,6,1 states and
1,4,3,24,16 solutions for q=0,3,4,5,6); the charts partition the 48 admissible solutions. -/
theorem K4_statewise_chart_counts {a : Fin 6 → ℂ} (ha : ∀ e, a e ≠ 0) (ha1 : ∀ e, a e ^ 2 ≠ 1) :
    ∃ (ω : Finset (Fin 6) → Fin 4 → ℂ) (Q : Finset (Fin 6) → (Fin 4 → ℂ) → BP.Dart (Fin 6) → ℂ)
      (W : Finset (Fin 6) → (Fin 4 → ℂ) → Fin 4 → ℂ)
      (Φ : Finset (Fin 6) → OpenPartialHomeomorph (Fin 4 → ℂ) (Fin 4 → ℂ)),
      (∀ S, IsState K4 S → K4.IsPowerMapChart S a (ω S) (Q S) (W S) (Φ S)) ∧
      ∃ ε > 0, ∀ p : Fin 4 → ℂ, (∀ i, p i ≠ 0) → (∀ i, ‖p i‖ < ε) →
        (∀ S, IsState K4 S → Nat.card (K4.chartSols S (Q S) (W S) p) =
          if S.card = 6 then 16 else if S.card = 5 then 4 else 1) ∧
        (List.range 7).map (fun q =>
          (((Finset.univ.filter fun S : Finset (Fin 6) => S.card = q).filter (IsState K4)).card,
           Nat.card {y // ∃ S ∈ (Finset.univ.filter fun S : Finset (Fin 6) => S.card = q).filter
             (IsState K4), y ∈ K4.chartSols S (Q S) (W S) p})) =
          [(1, 1), (0, 0), (0, 0), (4, 4), (3, 3), (6, 24), (1, 16)] ∧
        (∀ y, K4.IsAdmissibleSolution a (fun i => (p i)⁻¹) y ↔
          ∃ S, IsState K4 S ∧ y ∈ K4.chartSols S (Q S) (W S) p) ∧
        (∀ S S' y, IsState K4 S → IsState K4 S' → y ∈ K4.chartSols S (Q S) (W S) p →
          y ∈ K4.chartSols S' (Q S') (W S') p → S = S') ∧
        Nat.card {y // K4.IsAdmissibleSolution a (fun i => (p i)⁻¹) y} = 48 := by
  obtain ⟨ω, Q, W, Φ, hc, ε, hε, h⟩ := exists_statewise_chart_counts K4 K4_loopless ha ha1
  refine ⟨ω, Q, W, Φ, hc, ε, hε, fun p hp hpε => ?_⟩
  obtain ⟨hcard, hpart, huniq, hT, htot, -⟩ := h p hp hpε
  refine ⟨fun S hS => (hcard S hS).trans (K4_state_wt S hS), ?_, hpart, huniq, htot.trans K4_Q⟩
  simp only [hT]
  decide

/-- **Statewise real chart counts of K₄ (`real:all-real-states`, `sf:k4-states`,
`fig:k4-states`).** For real a_e>0, a_e≠1 there are power-map charts, one for each state and with
positive real root tuples, such that for all sufficiently small real p>0, at b=p⁻¹: the chart
of a state has 16, 4 or 1 complex solutions as in `K4_statewise_chart_counts`, and exactly one
real solution for the empty set, the triangles and the four-cycles and none for K₄−e and K₄; by
edge count the complex and real totals are those of the table (real row 1,4,3,0,0 for
q=0,3,4,5,6); the admissible real solutions are exactly the real chart solutions of the eight
Eulerian states; the real chart solution of S is negative exactly on the edges of S, so it is
positive only for S=∅; and the complex and real totals are 48 and 8. -/
theorem K4_statewise_real_chart_counts {a : Fin 6 → ℝ} (ha : ∀ e, 0 < a e) (ha1 : ∀ e, a e ≠ 1) :
    ∃ (ω : Finset (Fin 6) → Fin 4 → ℂ) (Q : Finset (Fin 6) → (Fin 4 → ℂ) → BP.Dart (Fin 6) → ℂ)
      (W : Finset (Fin 6) → (Fin 4 → ℂ) → Fin 4 → ℂ)
      (Φ : Finset (Fin 6) → OpenPartialHomeomorph (Fin 4 → ℂ) (Fin 4 → ℂ)),
      (∀ S, IsState K4 S → K4.IsPowerMapChart S (fun e => (a e : ℂ)) (ω S) (Q S) (W S) (Φ S) ∧
        ∀ i, ∃ w : ℝ, 0 < w ∧ ω S i = w) ∧
      ∃ ε > 0, ∀ p : Fin 4 → ℝ, (∀ i, 0 < p i) → (∀ i, p i < ε) →
        (∀ S, IsState K4 S → Nat.card (K4.chartSols S (Q S) (W S) (fun i => (p i : ℂ))) =
          if S.card = 6 then 16 else if S.card = 5 then 4 else 1) ∧
        (∀ S, IsState K4 S → Nat.card {y : BP.Dart (Fin 6) → ℝ //
            (fun α => (y α : ℂ)) ∈ K4.chartSols S (Q S) (W S) (fun i => (p i : ℂ))} =
          if S.card ≤ 4 then 1 else 0) ∧
        (List.range 7).map (fun q =>
          (((Finset.univ.filter fun S : Finset (Fin 6) => S.card = q).filter (IsState K4)).card,
           Nat.card {y // ∃ S ∈ (Finset.univ.filter fun S : Finset (Fin 6) => S.card = q).filter
             (IsState K4), y ∈ K4.chartSols S (Q S) (W S) (fun i => (p i : ℂ))},
           Nat.card {y : BP.Dart (Fin 6) → ℝ // ∃ S ∈ (Finset.univ.filter
             fun S : Finset (Fin 6) => S.card = q).filter (IsState K4),
             (fun α => (y α : ℂ)) ∈ K4.chartSols S (Q S) (W S) (fun i => (p i : ℂ))})) =
          [(1, 1, 1), (0, 0, 0), (0, 0, 0), (4, 4, 4), (3, 3, 3), (6, 24, 0), (1, 16, 0)] ∧
        (∀ y : BP.Dart (Fin 6) → ℝ, K4.IsAdmissibleSolution a (fun i => (p i)⁻¹) y ↔
          ∃ S, IsState K4 S ∧ S.card ≤ 4 ∧
            (fun α => (y α : ℂ)) ∈ K4.chartSols S (Q S) (W S) (fun i => (p i : ℂ))) ∧
        (∀ S, IsState K4 S → ∀ y : BP.Dart (Fin 6) → ℝ,
          (fun α => (y α : ℂ)) ∈ K4.chartSols S (Q S) (W S) (fun i => (p i : ℂ)) →
            BP.negSupport y = S ∧ ((∀ α, 0 < y α) ↔ S = ∅)) ∧
        Nat.card {y // K4.IsAdmissibleSolution (fun e => (a e : ℂ)) (fun i => ((p i : ℂ))⁻¹) y} =
          48 ∧
        Nat.card {y : BP.Dart (Fin 6) → ℝ // K4.IsAdmissibleSolution a (fun i => (p i)⁻¹) y} =
          8 := by
  obtain ⟨ω, Q, W, Φ, hc, ε, hε, h⟩ :=
    exists_statewise_real_chart_counts K4 K4_loopless ha ha1
  refine ⟨ω, Q, W, Φ, hc, ε, hε, fun p hp hpε => ?_⟩
  obtain ⟨hcard, -, -, hT, htot, hreal, -, hrpart, hneg, -, hrT, hrtot⟩ := h p hp hpε
  refine ⟨fun S hS => (hcard S hS).trans (K4_state_wt S hS), fun S hS => ?_, ?_, fun y => ?_,
    hneg, htot.trans K4_Q, hrtot.trans K4_evenSets⟩
  · rw [hreal S hS]
    simp only [K4_state_isEvenSet_iff S hS]
  · simp only [hT, hrT]
    decide
  · rw [hrpart]
    simp only [K4_isEvenSet_iff_isState, and_assoc]

end BPFixedPoints.Examples
