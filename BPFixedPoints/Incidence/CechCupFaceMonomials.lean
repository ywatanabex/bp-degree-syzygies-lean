import BPFixedPoints.Incidence.CechCupFormula
import BPFixedPoints.Incidence.CechCubicalCellDiagonalSupport
import BPFixedPoints.Incidence.CechTwistRestrictionMonomials

/-! # The original tensor cup monomials in the original mixed face coordinates -/

namespace BPFixedPoints.CechProduct
open Finsupp CechCubicalCell
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section

private theorem lineCupBasis_face_shape (s p q : Fin 3)
    (h : intervalDiagonalShape s p q) (hp : p=s ∨ s=2) (hq : q=s ∨ s=2)
    (d e : ℕ) (m : FaceExponent p) (k : FaceExponent q) :
    lineCupBasis e (vertexFaceEquiv.symm ⟨p,m⟩) (vertexFaceEquiv.symm ⟨q,k⟩) =
      some (vertexFaceEquiv.symm ⟨s,
        (refinementCoordinate hp m + (if p=1 ∧ s=2 then exponentFromInt s (-(d : ℤ)) else 0)) +
        (refinementCoordinate hq k + (if q=1 ∧ s=2 then exponentFromInt s (-(e : ℤ)) else 0))⟩) := by
  fin_cases s <;> fin_cases p <;> fin_cases q <;>
    simp only [intervalDiagonalShape] at h <;> simp_all [lineCupBasis,vertexFaceEquiv,
      refinementCoordinate,exponentToInt,exponentFromInt,FaceExponent]
  all_goals try rfl
  change ℤ at m
  change ℕ at k
  change m + (-(e : ℤ) - (k : ℤ)) = m + (-(k : ℤ) + -(e : ℤ))
  omega

variable {V : Type} [Fintype V]

/-- The original coefficient product uses the two original exponent refinements and twist shifts. -/
def cupFaceExponent (d e : V → ℕ) {s p q : V → Fin 3} (h : DiagonalShape s p q)
    (m : FaceMonoid p) (k : FaceMonoid q) : FaceMonoid s :=
  (refinementExponent h.left_refines m + twistRestrictionShift h.left_refines (fun v => -(d v : ℤ))) +
    (refinementExponent h.right_refines k + twistRestrictionShift h.right_refines (fun v => -(e v : ℤ)))

/-- Each original allowed cell pair gives exactly the original tensor cup monomial. -/
theorem cupBasis_embedFace (d e : V → ℕ) {s p q : V → Fin 3} (h : DiagonalShape s p q)
    (m : FaceMonoid p) (k : FaceMonoid q) :
    cupBasis e (embedFace p m) (embedFace q k) = some (embedFace s (cupFaceExponent d e h m k)) := by
  apply (cupBasis_some_iff _ _ _ _).mpr
  intro v
  exact lineCupBasis_face_shape (s v) (p v) (q v) (h v) (h.left_refines v) (h.right_refines v)
    (d v) (e v) (m v) (k v)

private theorem lineCupBasis_output_shape {e : ℕ} {x y z : Basis}
    (h : lineCupBasis e x y = some z) :
    intervalDiagonalShape (vertexFaceEquiv z).1 (vertexFaceEquiv x).1 (vertexFaceEquiv y).1 := by
  rcases x with x | x | x <;> rcases y with y | y | y <;>
    simp only [lineCupBasis,Option.some.injEq,reduceCtorEq] at h <;> cases h <;>
    simp [vertexFaceEquiv,intervalDiagonalShape]

/-- Every original nonzero tensor cup has exactly an original Alexander--Whitney face shape. -/
theorem cupBasis_output_shape (e : V → ℕ) {x y z : V → Basis} (h : cupBasis e x y=some z) :
    DiagonalShape (faceBasisEquiv z).1 (faceBasisEquiv x).1 (faceBasisEquiv y).1 := by
  intro v
  exact lineCupBasis_output_shape ((cupBasis_some_iff _ _ _ _).mp h v)

private theorem finCupCross_embedFace (n : ℕ) (p q : Fin n → Fin 3)
    (m : FaceMonoid p) (k : FaceMonoid q) :
    finCupCross n (embedFace p m) (embedFace q k) = finDiagonalCross n p q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change cechDegree (embedFace (Fin.tail p) (fun v => m v.succ)) *
      lineDegree (vertexFaceEquiv.symm ⟨q 0,k 0⟩) +
        finCupCross n (embedFace (Fin.tail p) (fun v => m v.succ))
          (embedFace (Fin.tail q) (fun v => k v.succ)) = _
    rw [cechDegree_embedFace,ih]
    have hl (z : Fin 3) (a : FaceExponent z) :
        lineDegree (vertexFaceEquiv.symm ⟨z,a⟩) = if z=2 then 1 else 0 := by
      fin_cases z <;> rfl
    have h := hl (q 0) (k 0)
    rw [h]
    rfl

/-- The original tensor product crossing is precisely the crossing of the original cell diagonal. -/
theorem cupCross_embedFace (p q : V → Fin 3) (m : FaceMonoid p) (k : FaceMonoid q) :
    cupCross (embedFace p m) (embedFace q k) = diagonalCross p q :=
  finCupCross_embedFace _ _ _ _ _

end
end BPFixedPoints.CechProduct
