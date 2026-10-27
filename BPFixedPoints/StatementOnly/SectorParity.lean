import BPFixedPoints.Real.SectorBounds
import BPFixedPoints.Real.SectorOddness

/-!
# Sectorwise odd real-root counts (`real:sector-parity`)

For fixed finite nonzero couplings J and Eulerian S, if all admissible real
roots with negative set S are nondegenerate, they are finite in number and
odd. In particular nondegenerate positive roots have odd count.
Normalize 𝔥_S by its diagonal linear part, obtaining a bounded perturbation
of identity. A determinant integral for boundary-fixing maps and change of
variables in inverse charts prove that local determinant signs sum to one
(`odd_card_fiber_sub_of_bounded`), hence the number of zeros is odd.
Nondegeneracy is the real BP message Jacobian condition `IsSimpleSolution`.
Differentiate the BP residual and left inverse ½log F to transfer invertibility
to injectivity of the vertex derivative
(`fderiv_sectorField_injective_of_isSimpleSolution`).
-/

namespace BPFixedPoints

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] {G : Multigraph V E}

/-- **`real:sector-parity`.** If all admissible real roots with Eulerian negative set S are nondegenerate, there are finitely many and their count is odd. -/
theorem sector_count_odd (hG : G.Loopless) {a : E → ℝ} (ha : ∀ e, 0 < a e) (ha1 : ∀ e, a e ≠ 1)
    {b : V → ℝ} (hb : ∀ i, 0 < b i) {S : Finset E} (hS : G.IsEvenSet S)
    (hnd : ∀ y, G.IsAdmissibleSolution a b y → negSupport y = S → G.IsSimpleSolution a b y) :
    {y : Dart E → ℝ | G.IsAdmissibleSolution a b y ∧ negSupport y = S}.Finite ∧
      Odd (Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ negSupport y = S}) := by
  exact ⟨finite_sector_solutions_of_nondegenerate hG ha ha1 hb hS hnd,
    odd_card_sector_solutions hG ha ha1 hb hS hnd⟩

/-- For an admissible real solution, empty negative-edge set is equivalent to all messages positive. -/
theorem negSupport_eq_empty_iff (hG : G.Loopless) {a : E → ℝ} (ha : ∀ e, 0 < a e) {b : V → ℝ}
    (hb : ∀ i, 0 < b i) {y : Dart E → ℝ} (hy : G.IsAdmissibleSolution a b y) :
    negSupport y = ∅ ↔ ∀ α, 0 < y α := by
  have hsign := (real_sign_sectors hG ha hb hy).2.1
  have hy0 := hy.2.1
  constructor
  · intro h α
    rcases α with ⟨e, d⟩
    have he : ¬ y (e, true) < 0 := by
      intro hneg
      have : e ∈ negSupport y := by simp [negSupport, hneg]
      rw [h] at this; simp at this
    cases d
    · have h2 : ¬ y (e, false) < 0 := by
        intro hneg
        exact he ((hsign (e, false)).1 hneg)
      exact lt_of_le_of_ne (not_lt.1 h2) (hy0 (e, false)).symm
    · exact lt_of_le_of_ne (not_lt.1 he) (hy0 (e, true)).symm
  · intro h
    ext e
    simp only [negSupport, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false, not_lt]
    exact (h (e, true)).le

/-- **Corollary of `sector_count_odd`.** If all positive roots are nondegenerate, their count is odd. -/
theorem positive_count_odd (hG : G.Loopless) {a : E → ℝ} (ha : ∀ e, 0 < a e) (ha1 : ∀ e, a e ≠ 1)
    {b : V → ℝ} (hb : ∀ i, 0 < b i)
    (hnd : ∀ y, G.IsAdmissibleSolution a b y → (∀ α, 0 < y α) → G.IsSimpleSolution a b y) :
    Odd (Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α}) := by
  have h := (sector_count_odd hG ha ha1 hb (S := ∅) (fun v => by simp)
    (fun y hy hS => hnd y hy ((negSupport_eq_empty_iff hG ha hb hy).1 hS))).2
  have e : {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ negSupport y = ∅} ≃
      {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} :=
    Equiv.subtypeEquivRight fun y => ⟨fun h => ⟨h.1, (negSupport_eq_empty_iff hG ha hb h.1).1 h.2⟩,
      fun h => ⟨h.1, (negSupport_eq_empty_iff hG ha hb h.1).2 h.2⟩⟩
  rwa [← Nat.card_congr e]

end Multigraph

end BPFixedPoints

