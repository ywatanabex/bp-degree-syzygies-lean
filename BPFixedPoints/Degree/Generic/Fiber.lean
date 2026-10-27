import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Polynomial solutions and simplicity: abstract language

Fix a square system f:ι→R[X_ι] over a commutative ring and a denominator D.
For θ:R→κ to a field, `SystemSolutions f D θ` consists of zeros with nonzero
denominator; `IsSimpleAt f θ y` means a nonzero Jacobian determinant.

`generic_fiber_constancy` in `Generic/FiberConstancy.lean` states: if an
injective θ₀:R→Ω to an algebraically closed characteristic-zero field has
finitely many solutions, exactly Q, all simple, then some nonzero g∈R ensures
the same conclusion for every θ:R→κ to an algebraically closed field with
θ(g)≠0. This statement was previously an axiom.
-/

namespace BPFixedPoints.BP

open MvPolynomial

universe u v w x

/-- Solutions of f over κ after coefficient specialization by θ, with denominator D nonzero. -/
abbrev SystemSolutions {R : Type u} [CommRing R] {ι : Type v} (f : ι → MvPolynomial ι R)
    (D : MvPolynomial ι R) {κ : Type w} [CommRing κ] (θ : R →+* κ) : Type (max v w) :=
  {y : ι → κ // (∀ i, eval y (map θ (f i)) = 0) ∧ eval y (map θ D) ≠ 0}

/-- Simplicity at y: the Jacobian determinant is nonzero. -/
def IsSimpleAt {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (f : ι → MvPolynomial ι R) {κ : Type w} [CommRing κ] (θ : R →+* κ) (y : ι → κ) : Prop :=
  (Matrix.of fun i j => eval y (pderiv j (map θ (f i)))).det ≠ 0

end BPFixedPoints.BP
