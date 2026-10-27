import BPFixedPoints.Incidence.CechFaceMaps
import BPFixedPoints.Incidence.ResolutionStates

/-! # Actual incidence equations on each Čech face -/

namespace BPFixedPoints.CechProduct

variable (R : Type*) [CommRing R]

theorem faceVertex_monomial {V : Type*} [DecidableEq V]
    (q : V → Fin 3) (v : V) (α : Fin 2) :
    AddMonoidAlgebra.single (faceVertexExponent q v α.val (1 - α.val)) (1 : R) =
      Multigraph.incCoord (decide (q v = 1)) α (faceVariable R q v) := by
  unfold faceVertexExponent
  rw [faceShiftExponent_bit]
  fin_cases α <;> by_cases hq : q v = 1 <;>
    simp [Multigraph.incCoord, faceVariable, hq, AddMonoidAlgebra.one_def]

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Multigraph

open CechProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

theorem incFaceShift (q : V → Fin 3) (e : E) (α β : Fin 2) :
    faceShift q (G.incSectionLeft e α β) (G.incSectionRight e α β) =
      faceVertexExponent q (G.fst e) α.val (1 - α.val) +
        faceVertexExponent q (G.snd e) β.val (1 - β.val) := by
  ext v
  change faceShiftExponent (q v)
      ((if G.fst e = v then α.val else 0) + (if G.snd e = v then β.val else 0))
      ((if G.fst e = v then 1 - α.val else 0) +
        (if G.snd e = v then 1 - β.val else 0)) = _
  rw [faceShiftExponent_add]
  have h (w : V) (a b : ℕ) :
      faceShiftExponent (q v) (if w = v then a else 0) (if w = v then b else 0) =
        faceVertexExponent q w a b v := by
    by_cases hw : w = v
    · subst w
      simp [faceVertexExponent]
    · simp [faceVertexExponent, hw, Pi.single_eq_of_ne (Ne.symm hw)]
  exact congrArg₂ (· + ·) (h (G.fst e) α.val (1 - α.val))
    (h (G.snd e) β.val (1 - β.val))

theorem incFaceShift_monomial (R : Type*) [CommRing R]
    (q : V → Fin 3) (e : E) (α β : Fin 2) :
    AddMonoidAlgebra.single
        (faceShift q (G.incSectionLeft e α β) (G.incSectionRight e α β)) (1 : R) =
      incCoord (decide (q (G.fst e) = 1)) α (faceVariable R q (G.fst e)) *
        incCoord (decide (q (G.snd e) = 1)) β (faceVariable R q (G.snd e)) := by
  rw [G.incFaceShift]
  rw [← one_mul (1 : R), ← AddMonoidAlgebra.single_mul_single,
    faceVertex_monomial, faceVertex_monomial]

/-- The universal four-term incidence equation on each face. -/
noncomputable def incFaceEquation (q : V → Fin 3) (e : E) :
    MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q) :=
  ∑ α : Fin 2, ∑ β : Fin 2,
    MvPolynomial.X (e, α, β) *
      MvPolynomial.C (incCoord (decide (q (G.fst e) = 1)) α
        (faceVariable ℂ q (G.fst e))) *
      MvPolynomial.C (incCoord (decide (q (G.snd e) = 1)) β
        (faceVariable ℂ q (G.snd e)))

theorem polynomialFaceEquiv_incSection (q : V → Fin 3) (e : E)
    (x : C (IncCoeffRing E) V) :
    polynomialFaceEquiv ℂ (IncCoeffIdx E)
      ((∑ α : Fin 2, ∑ β : Fin 2,
        (MvPolynomial.X (e, α, β) : IncCoeffRing E) •
          multiply (IncCoeffRing E) (G.incSectionLeft e α β)
            (G.incSectionRight e α β)) x) q =
      G.incFaceEquation q e * polynomialFaceEquiv ℂ (IncCoeffIdx E) x q := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, Finset.sum_apply,
    polynomialFaceEquiv_X_smul_multiply, incFaceEquation, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  rw [G.incFaceShift_monomial, map_mul]
  ring

end BPFixedPoints.Multigraph
