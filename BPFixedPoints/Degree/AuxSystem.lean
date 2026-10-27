import BPFixedPoints.Degree.Equations

/-!
# Auxiliary system

For parameters (s_e,β_i) and unknowns (A_{e,i},F_i), impose A≠0,−1, F≠0,−1 and
F_i(1+A_{e,j})=A_{e,i}(1+s_e A_{e,j}) (4), with denominators cleared, and
β_i=F_i^{1−d_i}∏_{e∋i}A_{e,i} (5).
`isAuxSolution_of_admissible` gives these equations from admissible BP solutions;
`Degree/Inverse.lean` reconstructs BP solutions in the reverse direction.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Aux

variable {K : Type*} [Field K]

/-- Auxiliary system with parameters (s,β), unknowns (A,F), nonvanishing conditions A≠0,−1, F≠0,−1 and equations (4)–(5). -/
structure IsAuxSolution (s : E → K) (β : V → K) (A : Dart E → K) (F : V → K) : Prop where
  A_ne_zero : ∀ α, A α ≠ 0
  A_ne_neg_one : ∀ α, A α ≠ -1
  F_ne_zero : ∀ i, F i ≠ 0
  F_ne_neg_one : ∀ i, F i ≠ -1
  edge : ∀ α, F (G.tail α) * (1 + A (rev α)) = A α * (1 + s α.1 * A (rev α))
  vertex : ∀ i, β i = F i ^ ((1 : ℤ) - G.degree i) * ∏ α ∈ G.inDarts i, A (rev α)

/-- Auxiliary coordinates of an admissible BP solution solve the auxiliary system (forward implication, proved). -/
theorem isAuxSolution_of_admissible (hG : G.Loopless) (a : E → K) (b : V → K) (y : Dart E → K)
    (ha : ∀ e, a e ≠ 0) (hb : ∀ i, b i ≠ 0) (h : G.IsAdmissibleSolution a b y) :
    G.IsAuxSolution (fun e => a e ^ 2) (G.auxBeta a b) (G.auxA a b y) (G.totalField b y) where
  A_ne_zero := G.auxA_ne_zero a b y ha hb h.2.1
  A_ne_neg_one := G.auxA_ne_neg_one a b y ha h.2.2.1
  F_ne_zero := G.totalField_ne_zero b y hb h.2.1
  F_ne_neg_one i := fun h0 => h.2.2.2 i (by rw [h0]; ring)
  edge α := by
    have hB : 1 + G.auxA a b y (rev α) ≠ 0 := by
      intro h0
      exact G.auxA_ne_neg_one a b y ha h.2.2.1 (rev α) (by linear_combination h0)
    have := G.field_eq_auxA a b y h.1 ha h.2.2.1 α
    rw [eq_div_iff hB] at this
    exact this
  vertex := G.auxBeta_eq a b y hG ha hb h.2.1

end Aux

end Multigraph

end BPFixedPoints
