import BPFixedPoints.Degree.Limit.Points
import BPFixedPoints.Degree.Inverse
import BPFixedPoints.Degree.AuxSystem
import BPFixedPoints.Degree.Jacobian
import BPFixedPoints.Degree.Generic.Count
import BPFixedPoints.Degree.Generic.SimpleTransfer
import BPFixedPoints.Degree.WeakCoupling.Line

/-!
# Final statements of N=Q and weak coupling

All theorems here are free of `sorry` and named axioms; `#print axioms` lists
only the three standard axioms.

* `IsAuxSolution` is in `Degree/AuxSystem.lean`; valued boundary exclusion is
  `boundary_exclusion` in `Degree/Boundary/Exclusion.lean`.
* Multivariate `hensel_lift` is in `Degree/Lift/Hensel.lean`.
  `exists_Q_formal_solutions` in `Degree/Lift/Formal.lean` gives unique K⟦t⟧
  lifts of limit points and Q(G) distinct admissible formal solutions.
* `card_puiseuxSolutions` in `Degree/Lift/Count.lean` gives exactly Q(G)
  admissible solutions for s_e=1+t c_e over L. `newtonPuiseux_exists` in
  `Degree/Boundary/ValuedFieldExists.lean` constructs L.
* `generic_fiber_constancy` in `Degree/Generic/FiberConstancy.lean` yields a
  nonzero P∈ℤ[a,b] whose nonvanishing locus has exactly Q(G) admissible BP
  solutions, with simple auxiliary coordinates (`exists_generic_count_eq_Q`
  in `Degree/Generic/Count.lean`).
* `isSimpleSolution_of_isSimpleAuxSolution` in `Degree/Generic/SimpleTransfer.lean`
  transfers simplicity to BP coordinates, completing `exists_generic_degree_eq_Q`.
* `card_weak_coupling_eq_Q` in `Degree/WeakCoupling/Line.lean` gives exactly
  Q(G) simple solutions for fixed c,β and sufficiently small complex ε≠0
  along s=1+εc. Its corollary `exists_weak_coupling_branches` gives at least Q(G).
  Convergence of branches to limit points as ε→0 is not formalized.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Complex

/-- **Fixed parameters.** For fixed c_e≠0 and β_i≠0,−1, sufficiently small ε≠0 gives at least Q(G) admissible auxiliary solutions at s_e=1+εc_e; in fact exactly Q(G), all simple, by `card_weak_coupling_eq_Q`. -/
theorem exists_weak_coupling_branches (c : E → ℂ) (hc : ∀ e, c e ≠ 0)
    (β : V → ℂ) (hβ0 : ∀ i, β i ≠ 0) (hβ1 : ∀ i, β i ≠ -1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℂ, ε ≠ 0 → ‖ε‖ < ε₀ →
      G.Q ≤ Nat.card {p : (Dart E → ℂ) × (V → ℂ) //
        G.IsAuxSolution (fun e => 1 + ε * c e) β p.1 p.2} := by
  obtain ⟨ε₀, hε₀, h⟩ := G.card_weak_coupling_eq_Q c hc β hβ0 hβ1
  exact ⟨ε₀, hε₀, fun ε hε hε' => (h ε hε hε').1.ge⟩

end Complex

/-- **N=Q.** A nonzero P∈ℤ[a_e,b_i] exists such that every nonzero complex parameter with P(a,b)≠0 has exactly Q(G) admissible BP solutions, all simple in BP coordinates. Uses `exists_generic_count_eq_Q` and `isSimpleSolution_of_isSimpleAuxSolution` in `Degree/Generic/SimpleTransfer.lean`, without `sorry` or named axioms. -/
theorem exists_generic_degree_eq_Q (hG : G.Loopless) :
    ∃ P : MvPolynomial (E ⊕ V) ℤ, P ≠ 0 ∧
      ∀ (a : E → ℂ) (b : V → ℂ), (∀ e, a e ≠ 0) → (∀ i, b i ≠ 0) →
        MvPolynomial.eval (Sum.elim a b) (MvPolynomial.map (Int.castRingHom ℂ) P) ≠ 0 →
          Nat.card {y : Dart E → ℂ // G.IsAdmissibleSolution a b y} = G.Q ∧
          ∀ y, G.IsAdmissibleSolution a b y → G.IsSimpleSolution a b y := by
  obtain ⟨P, hP0, hP⟩ := G.exists_generic_count_eq_Q hG
  refine ⟨P, hP0, fun a b ha hb hne => ?_⟩
  obtain ⟨hcard, hsimp⟩ := hP ℂ a b ha hb hne
  exact ⟨hcard, fun y hy =>
    G.isSimpleSolution_of_isSimpleAuxSolution a b y hG ha hb hy (hsimp y hy)⟩

/-- **Counting statement over ℂ.** No `sorry` or additional axioms. -/
theorem exists_generic_count_eq_Q_complex (hG : G.Loopless) :
    ∃ P : MvPolynomial (E ⊕ V) ℤ, P ≠ 0 ∧
      ∀ (a : E → ℂ) (b : V → ℂ), (∀ e, a e ≠ 0) → (∀ i, b i ≠ 0) →
        MvPolynomial.eval (Sum.elim a b) (MvPolynomial.map (Int.castRingHom ℂ) P) ≠ 0 →
          Nat.card {y : Dart E → ℂ // G.IsAdmissibleSolution a b y} = G.Q := by
  obtain ⟨P, hP0, hP⟩ := G.exists_generic_count_eq_Q hG
  exact ⟨P, hP0, fun a b ha hb hne => (hP ℂ a b ha hb hne).1⟩

end Multigraph

end BPFixedPoints
