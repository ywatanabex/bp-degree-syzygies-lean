import BPFixedPoints.Degree.Equations

/-!
# Polynomial BP equations and Jacobian

Represent f_α for fixed parameters (a,b) by `bpMvPoly a b α∈K[y]`.
Define `jacobian a b y` using `MvPolynomial.pderiv`, with entry
∂f_α/∂y_γ evaluated at y. A solution is simple when its Jacobian determinant
is nonzero; this expresses simplicity in the generic admissible fiber.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP MvPolynomial

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)
variable {K : Type*} [Field K]

/-- Cavity-field polynomial X_α=b_{t(α)}∏_{γ∈in(t(α))∖{ᾱ}}y_γ. -/
noncomputable def cavityPoly (b : V → K) (α : Dart E) : MvPolynomial (Dart E) K :=
  C (b (G.tail α)) * ∏ γ ∈ (G.inDarts (G.tail α)).erase (rev α), X γ

/-- Polynomial BP equation f_α=y_α(X_α+a_e)−(a_e X_α+1). -/
noncomputable def bpMvPoly (a : E → K) (b : V → K) (α : Dart E) : MvPolynomial (Dart E) K :=
  X α * (G.cavityPoly b α + C (a α.1)) - (C (a α.1) * G.cavityPoly b α + 1)

theorem eval_cavityPoly (b : V → K) (y : Dart E → K) (α : Dart E) :
    eval y (G.cavityPoly b α) = G.cavity b y α := by
  simp [cavityPoly, cavity, eval_prod]

theorem eval_bpMvPoly (a : E → K) (b : V → K) (y : Dart E → K) (α : Dart E) :
    eval y (G.bpMvPoly a b α) = G.bpPoly a b y α := by
  simp [bpMvPoly, bpPoly, eval_cavityPoly]

/-- Zeros of the polynomial representation are precisely polynomial fixed points. -/
theorem isFixedPoint_iff_eval (a : E → K) (b : V → K) (y : Dart E → K) :
    G.IsFixedPoint a b y ↔ ∀ α, eval y (G.bpMvPoly a b α) = 0 := by
  simp [IsFixedPoint, eval_bpMvPoly]

/-- Jacobian matrix with (α,γ) entry ∂f_α/∂y_γ evaluated at y. -/
noncomputable def jacobian (a : E → K) (b : V → K) (y : Dart E → K) :
    Matrix (Dart E) (Dart E) K :=
  fun α γ => eval y (pderiv γ (G.bpMvPoly a b α))

/-- A solution y is simple if its Jacobian determinant is nonzero. -/
def IsSimpleSolution (a : E → K) (b : V → K) (y : Dart E → K) : Prop :=
  (G.jacobian a b y).det ≠ 0

end Multigraph

end BPFixedPoints
