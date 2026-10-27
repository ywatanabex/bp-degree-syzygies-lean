import BPFixedPoints.StrongField.StatewiseChartCounts
import BPFixedPoints.Real.StrongFieldCount

/-!
# Statewise chart counts in every field orthant (`real:all-real-states`, `real:spin-gauge`)

The last sentence of Remark `real:all-real-states`: the spin change `real:spin-gauge` transports
the statewise counts of `StrongField/StatewiseChartCounts.lean` from the positive orthant
(small p_i>0, i.e. b_i→+∞) to every field orthant. For signs η:V→Bool (true meaning h_i→−∞),
put a'=`gaugeA η a` (a'_e=a_e^{±1}, still positive and ≠1) and take the statewise charts of a'.
At b=`gaugeB η p⁻¹` (b_i=p_i⁻¹ if η_i is false and b_i=p_i if η_i is true) the chart of a state S
is transported by the gauge y ↦ `gaugeY η y` (y_α ↦ y_α^{±1}), which is an involution, commutes
with the inclusion ℝ→ℂ (`gaugeY_ofReal`) and preserves message signs (`negSupport_gaugeY`).
`exists_statewise_real_chart_counts_of_orthant` gives, for all sufficiently small p>0: wt(S)
complex solutions in the transported chart of each state, partitioning the Q(G) admissible
complex solutions; exactly one real solution if S is Eulerian and none otherwise; the admissible
real solutions are the real transported chart solutions of the Eulerian states, the chart of S
is the sign sector S, and there are #{Eulerian S} real solutions.

The orthant charts are the gauge transports of the positive-orthant charts of a'; no new
analytic chart is constructed.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Orthant

variable (η : V → Bool)

/-- x^{±1} commutes with the inclusion ℝ→ℂ. -/
theorem flipPow_ofReal (s : Bool) (x : ℝ) : flipPow s (x : ℂ) = ((flipPow s x : ℝ) : ℂ) := by
  cases s <;> simp [flipPow]

/-- The gauge of messages commutes with the inclusion ℝ→ℂ. -/
theorem gaugeY_ofReal (y : Dart E → ℝ) :
    G.gaugeY η (fun α => (y α : ℂ)) = fun α => ((G.gaugeY η y α : ℝ) : ℂ) := by
  funext α
  exact flipPow_ofReal _ _

/-- The gauge of couplings commutes with the inclusion ℝ→ℂ. -/
theorem gaugeA_ofReal (a : E → ℝ) :
    G.gaugeA η (fun e => (a e : ℂ)) = fun e => ((G.gaugeA η a e : ℝ) : ℂ) := by
  funext e
  exact flipPow_ofReal _ _

/-- The gauge of fields commutes with the inclusion ℝ→ℂ. -/
theorem gaugeB_ofReal (b : V → ℝ) :
    gaugeB η (fun i => (b i : ℂ)) = fun i => ((gaugeB η b i : ℝ) : ℂ) := by
  funext i
  exact flipPow_ofReal _ _

/-- The gauge preserves the sign of every message, hence the negative-edge set. -/
theorem negSupport_gaugeY (y : Dart E → ℝ) : negSupport (G.gaugeY η y) = negSupport y := by
  ext e
  unfold negSupport
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, gaugeY, flipPow]
  split_ifs
  · exact inv_lt_zero
  · rfl

/-- The gauge preserves positivity of the couplings. -/
theorem gaugeA_pos {a : E → ℝ} (ha : ∀ e, 0 < a e) (e : E) : 0 < G.gaugeA η a e := by
  unfold gaugeA flipPow
  split_ifs
  · exact inv_pos.2 (ha e)
  · exact ha e

/-- The gauge preserves a_e≠1. -/
theorem gaugeA_ne_one {a : E → ℝ} (ha1 : ∀ e, a e ≠ 1) (e : E) : G.gaugeA η a e ≠ 1 := by
  unfold gaugeA flipPow
  split_ifs
  · exact fun h => ha1 e (inv_eq_one.1 h)
  · exact ha1 e

variable {G η}

/-- **Spin gauge as an equivalence of admissibility.** -/
theorem isAdmissibleSolution_gauge_iff {K : Type*} [Field K] {a : E → K} {b : V → K}
    {y : Dart E → K} (ha : ∀ e, a e ≠ 0) (hb : ∀ i, b i ≠ 0) :
    G.IsAdmissibleSolution (G.gaugeA η a) (gaugeB η b) (G.gaugeY η y) ↔
      G.IsAdmissibleSolution a b y := by
  refine ⟨fun h => ?_, isAdmissibleSolution_gauge η ha hb⟩
  have := isAdmissibleSolution_gauge η (G.gaugeA_ne_zero η ha) (gaugeB_ne_zero η hb) h
  simpa using this

variable (G η)

/-- **Statewise counts in every field orthant (`real:all-real-states`, `real:spin-gauge`).** Fix
real a_e>0, a_e≠1 on a loopless graph and field signs η. There are power-map charts of
a'=`gaugeA η a`, one for every state S and with positive real root tuples, such that for all
sufficiently small real p>0, at the field b=`gaugeB η p⁻¹` of the orthant η, with the chart of S
transported by the gauge y ↦ `gaugeY η y`:
* the transported chart of S contains exactly wt(S) complex solutions, and the transported
  charts partition the admissible complex solutions;
* it contains exactly one real solution if S is Eulerian and none otherwise;
* the admissible real solutions are exactly the real transported chart solutions of the Eulerian
  states; such a solution of S has negative-edge set S; there are #{Eulerian S} of them. -/
theorem exists_statewise_real_chart_counts_of_orthant (hG : G.Loopless) {a : E → ℝ}
    (ha : ∀ e, 0 < a e) (ha1 : ∀ e, a e ≠ 1) :
    ∃ (ω : Finset E → V → ℂ) (Q : Finset E → (V → ℂ) → Dart E → ℂ)
      (W : Finset E → (V → ℂ) → V → ℂ) (Φ : Finset E → OpenPartialHomeomorph (V → ℂ) (V → ℂ)),
      (∀ S, IsState G S →
        G.IsPowerMapChart S (fun e => ((G.gaugeA η a e : ℝ) : ℂ)) (ω S) (Q S) (W S) (Φ S) ∧
        ∀ i, ∃ w : ℝ, 0 < w ∧ ω S i = w) ∧
      ∃ ε > 0, ∀ p : V → ℝ, (∀ i, 0 < p i) → (∀ i, p i < ε) →
        (∀ S, IsState G S → Nat.card {y : Dart E → ℂ //
            G.gaugeY η y ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ))} = G.wt phi S) ∧
        (∀ y : Dart E → ℂ, G.IsAdmissibleSolution (fun e => (a e : ℂ))
            (gaugeB η fun i => ((p i : ℂ))⁻¹) y ↔
          ∃ S, IsState G S ∧ G.gaugeY η y ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ))) ∧
        (∀ S S' y, IsState G S → IsState G S' →
          G.gaugeY η y ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ)) →
          G.gaugeY η y ∈ G.chartSols S' (Q S') (W S') (fun i => (p i : ℂ)) → S = S') ∧
        (∀ S, IsState G S → Nat.card {y : Dart E → ℝ //
            G.gaugeY η (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ))} =
          if G.IsEvenSet S then 1 else 0) ∧
        (∀ y : Dart E → ℝ, G.IsAdmissibleSolution a (gaugeB η fun i => (p i)⁻¹) y ↔
          ∃ S, G.IsEvenSet S ∧
            G.gaugeY η (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ))) ∧
        (∀ S, IsState G S → ∀ y : Dart E → ℝ,
          G.gaugeY η (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) (fun i => (p i : ℂ)) →
            negSupport y = S) ∧
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a (gaugeB η fun i => (p i)⁻¹) y} =
          (Finset.univ.filter G.IsEvenSet).card := by
  obtain ⟨ω, Q, W, Φ, hc, ε, hε, h⟩ := G.exists_statewise_real_chart_counts hG
    (G.gaugeA_pos η ha) (G.gaugeA_ne_one η ha1)
  refine ⟨ω, Q, W, Φ, hc, ε, hε, fun p hp hpε => ?_⟩
  obtain ⟨hcard, hpart, huniq, -, -, hreal, -, hrpart, hneg, -, -, hrtot⟩ := h p hp hpε
  set pC : V → ℂ := fun i => (p i : ℂ)
  have haC : ∀ e, ((a e : ℂ)) ≠ 0 := fun e => by exact_mod_cast (ha e).ne'
  have hbC : ∀ i, (gaugeB η fun i => (pC i)⁻¹) i ≠ 0 :=
    gaugeB_ne_zero η fun i => inv_ne_zero (by simp [pC, (hp i).ne'])
  have hb : ∀ i, (gaugeB η fun i => (p i)⁻¹) i ≠ 0 :=
    gaugeB_ne_zero η fun i => inv_ne_zero (hp i).ne'
  -- Complex messages: the gauge identifies the problem with the positive orthant of a'.
  have hadmC : ∀ y : Dart E → ℂ, G.IsAdmissibleSolution (fun e => (a e : ℂ))
      (gaugeB η fun i => (pC i)⁻¹) y ↔
        G.IsAdmissibleSolution (fun e => ((G.gaugeA η a e : ℝ) : ℂ)) (fun i => (pC i)⁻¹)
          (G.gaugeY η y) := by
    intro y
    rw [← isAdmissibleSolution_gauge_iff (η := η) haC hbC, gaugeA_ofReal, gaugeB_gaugeB]
  -- Real messages.
  have hadmR : ∀ y : Dart E → ℝ, G.IsAdmissibleSolution a (gaugeB η fun i => (p i)⁻¹) y ↔
      G.IsAdmissibleSolution (G.gaugeA η a) (fun i => (p i)⁻¹) (G.gaugeY η y) := by
    intro y
    rw [← isAdmissibleSolution_gauge_iff (η := η) (fun e => (ha e).ne') hb, gaugeB_gaugeB]
  -- Transport of chart sets along the involution y ↦ gaugeY η y.
  have hcardC : ∀ S, IsState G S → Nat.card {y : Dart E → ℂ //
      G.gaugeY η y ∈ G.chartSols S (Q S) (W S) pC} = G.wt phi S := by
    intro S hS
    rw [← hcard S hS]
    exact Nat.card_congr
      { toFun := fun y => ⟨G.gaugeY η y.1, y.2⟩
        invFun := fun y => ⟨G.gaugeY η y.1, by rw [gaugeY_gaugeY]; exact y.2⟩
        left_inv := fun y => Subtype.ext (gaugeY_gaugeY η y.1)
        right_inv := fun y => Subtype.ext (gaugeY_gaugeY η y.1) }
  have hrealT : ∀ S, IsState G S → Nat.card {y : Dart E → ℝ //
      G.gaugeY η (fun α => (y α : ℂ)) ∈ G.chartSols S (Q S) (W S) pC} =
        if G.IsEvenSet S then 1 else 0 := by
    intro S hS
    rw [← hreal S hS]
    exact Nat.card_congr
      { toFun := fun y => ⟨G.gaugeY η y.1, by rw [← gaugeY_ofReal]; exact y.2⟩
        invFun := fun y => ⟨G.gaugeY η y.1, by rw [gaugeY_ofReal, gaugeY_gaugeY]; exact y.2⟩
        left_inv := fun y => Subtype.ext (gaugeY_gaugeY η y.1)
        right_inv := fun y => Subtype.ext (gaugeY_gaugeY η y.1) }
  refine ⟨hcardC, fun y => ?_, fun S S' y hS hS' h h' => huniq S S' _ hS hS' h h', hrealT,
    fun y => ?_, fun S hS y hy => ?_, ?_⟩
  · rw [hadmC]
    exact hpart _
  · rw [hadmR, hrpart, gaugeY_ofReal]
  · rw [gaugeY_ofReal] at hy
    rw [← negSupport_gaugeY G η y]
    exact (hneg S hS _ hy).1
  · rw [← hrtot]
    exact Nat.card_congr
      { toFun := fun y => ⟨G.gaugeY η y.1, (hadmR y.1).1 y.2⟩
        invFun := fun y => ⟨G.gaugeY η y.1, (hadmR _).2 (by simp only [gaugeY_gaugeY]; exact y.2)⟩
        left_inv := fun y => Subtype.ext (gaugeY_gaugeY η y.1)
        right_inv := fun y => Subtype.ext (gaugeY_gaugeY η y.1) }

end Orthant

end Multigraph

end BPFixedPoints
