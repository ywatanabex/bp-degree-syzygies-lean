import BPFixedPoints.Degree.Main
import BPFixedPoints.StateSum.SharpBounds

/-!
# Generic degree of trees and unicyclic graphs

The connected bounds (ν−1)2^ν+2≤Q(G)≤U_ν (`sharp_bounds_of_connected`) give
Q=1 at ν=0 and Q=2 at ν=1. With `exists_generic_degree_eq_Q`, a connected
loopless tree, including a single vertex, has one simple generic admissible
complex BP solution. A unicyclic graph with attached trees, including two
parallel edges on two vertices, has two simple solutions.
Uniqueness of positive real solutions at positive real parameters and explicit
open sets U_n are not formalized; genericity here means P≠0 for a nonzero polynomial.
-/

namespace BPFixedPoints

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

/-- For a connected graph with ν=0 (a tree), Q(G)=1. -/
theorem Q_eq_one_of_cycleRank_eq_zero (hc : G.Connected) (h : G.cycleRank = 0) : G.Q = 1 := by
  have hb := G.sharp_bounds_of_connected hc
  rw [h] at hb
  simp only [CharP.cast_eq_zero, zero_sub, pow_zero, mul_one, U_zero] at hb
  omega

/-- For a connected graph with ν=1 (unicyclic), Q(G)=2. -/
theorem Q_eq_two_of_cycleRank_eq_one (hc : G.Connected) (h : G.cycleRank = 1) : G.Q = 2 := by
  have hb := G.sharp_bounds_of_connected hc
  rw [h] at hb
  simp only [Nat.cast_one, sub_self, pow_one, zero_mul, zero_add, U_one] at hb
  omega

/-- **Generic degree of a tree.** For connected loopless G with ν=0, some nonzero P∈ℤ[a,b] ensures exactly one simple admissible BP solution at every nonzero complex parameter with P≠0. -/
theorem exists_generic_degree_eq_one_of_tree (hG : G.Loopless) (hc : G.Connected)
    (h : G.cycleRank = 0) :
    ∃ P : MvPolynomial (E ⊕ V) ℤ, P ≠ 0 ∧
      ∀ (a : E → ℂ) (b : V → ℂ), (∀ e, a e ≠ 0) → (∀ i, b i ≠ 0) →
        MvPolynomial.eval (Sum.elim a b) (MvPolynomial.map (Int.castRingHom ℂ) P) ≠ 0 →
          Nat.card {y : Dart E → ℂ // G.IsAdmissibleSolution a b y} = 1 ∧
          ∀ y, G.IsAdmissibleSolution a b y → G.IsSimpleSolution a b y := by
  rw [← G.Q_eq_one_of_cycleRank_eq_zero hc h]
  exact G.exists_generic_degree_eq_Q hG

/-- **Generic degree of a unicyclic graph.** For connected loopless G with ν=1, some nonzero P∈ℤ[a,b] ensures exactly two simple admissible BP solutions at every nonzero complex parameter with P≠0. -/
theorem exists_generic_degree_eq_two_of_unicyclic (hG : G.Loopless) (hc : G.Connected)
    (h : G.cycleRank = 1) :
    ∃ P : MvPolynomial (E ⊕ V) ℤ, P ≠ 0 ∧
      ∀ (a : E → ℂ) (b : V → ℂ), (∀ e, a e ≠ 0) → (∀ i, b i ≠ 0) →
        MvPolynomial.eval (Sum.elim a b) (MvPolynomial.map (Int.castRingHom ℂ) P) ≠ 0 →
          Nat.card {y : Dart E → ℂ // G.IsAdmissibleSolution a b y} = 2 ∧
          ∀ y, G.IsAdmissibleSolution a b y → G.IsSimpleSolution a b y := by
  rw [← G.Q_eq_two_of_cycleRank_eq_one hc h]
  exact G.exists_generic_degree_eq_Q hG

end Multigraph

end BPFixedPoints
