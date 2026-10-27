import BPFixedPoints.Incidence.CechTwistRestrictionMonomials
import BPFixedPoints.Incidence.VertexProjectiveTwistRowH1
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! # Original two-face coefficients as one-variable Cech coefficients -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
variable (R : Type) [CommRing R]

/-- The original first-coordinate coefficient ring on one of its three faces. -/
abbrev TwoRowBase (b : Fin 3) := AddMonoidAlgebra R (FaceExponent b)

/-- Read the second exponent first, retaining both original vertex labels. -/
def twoRowExponentEquiv (b c : Fin 3) :
    FaceMonoid (![b,c] : Fin 2 → Fin 3) ≃ FaceExponent c × FaceExponent b where
  toFun m := (m 1,m 0)
  invFun p := Fin.cons p.2 (Fin.cons p.1 (fun i => Fin.elim0 i))
  left_inv m := by funext v; fin_cases v <;> rfl
  right_inv p := rfl

/-- The original face ring is the original second-variable coefficient family over the first-variable ring. -/
noncomputable def twoRowFaceCoordinates (b c : Fin 3) :
    FaceRing R (![b,c] : Fin 2 → Fin 3) ≃ₗ[R] FaceExponent c →₀ TwoRowBase R b :=
  (AddMonoidAlgebra.coeffLinearEquiv R).trans
    ((Finsupp.mapDomain.linearEquiv R R (twoRowExponentEquiv b c)).trans
      ((Finsupp.curryLinearEquiv R).trans
        (Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv R).symm)))

/-- Each original mixed monomial retains its second exponent and its original first-coordinate coefficient. -/
theorem twoRowFaceCoordinates_single (b c : Fin 3) (m : FaceMonoid (![b,c] : Fin 2 → Fin 3)) (r : R) :
    twoRowFaceCoordinates R b c (AddMonoidAlgebra.single m r) =
      single (m 1) (AddMonoidAlgebra.single (m 0) r) := by
  change Finsupp.mapRange (AddMonoidAlgebra.coeffLinearEquiv R).symm
    (map_zero (AddMonoidAlgebra.coeffLinearEquiv R).symm)
    ((Finsupp.mapDomain (twoRowExponentEquiv b c) (single m r)).curry) = _
  rw [mapDomain_single,curry_single,mapRange_single]
  rfl

/-- The two original corner coefficients in the original one-variable Cech module. -/
noncomputable def twoRowZeroCoordinates (b : Fin 3) :
    (FaceRing R (![b,0] : Fin 2 → Fin 3) × FaceRing R (![b,1] : Fin 2 → Fin 3)) ≃ₗ[R]
      CechLine.C0 (TwoRowBase R b) :=
  (twoRowFaceCoordinates R b 0).prodCongr (twoRowFaceCoordinates R b 1)

/-- The original row overlap coefficients in the original one-variable Laurent module. -/
noncomputable def twoRowOneCoordinates (b : Fin 3) :
    FaceRing R (![b,2] : Fin 2 → Fin 3) ≃ₗ[R] CechLine.C1 (TwoRowBase R b) :=
  twoRowFaceCoordinates R b 2

private theorem row_refinement_first (d : Fin 2 → ℕ) (b c : Fin 3)
    (m : FaceMonoid (![b,c] : Fin 2 → Fin 3)) :
    (refinementExponent (twoRowFaceRefines b c) m +
      twistRestrictionShift (twoRowFaceRefines b c) (fun v => -(d v : ℤ))) 0 = m 0 := by
  apply exponentToInt_injective b
  change faceToInt (![b,2] : Fin 2 → Fin 3) (_ + _) 0 = faceToInt (![b,c] : Fin 2 → Fin 3) m 0
  rw [map_add,Pi.add_apply,faceToInt_refinement,faceToInt_twistRestrictionShift]
  have hb : ¬(b = 1 ∧ b = 2) := by omega
  simp only [Matrix.cons_val_zero,hb,ite_false,add_zero]

private theorem row_refinement_second (d : Fin 2 → ℕ) (b c : Fin 3)
    (m : FaceMonoid (![b,c] : Fin 2 → Fin 3)) :
    (refinementExponent (twoRowFaceRefines b c) m +
      twistRestrictionShift (twoRowFaceRefines b c) (fun v => -(d v : ℤ))) 1 =
      if c = 1 then -(d 1 : ℤ) - exponentToInt c (m 1) else exponentToInt c (m 1) := by
  change faceToInt (![b,2] : Fin 2 → Fin 3) (_ + _) 1 = _
  rw [map_add,Pi.add_apply,faceToInt_refinement,faceToInt_twistRestrictionShift]
  simp only [Matrix.cons_val_one,Matrix.cons_val_zero,and_true]
  split_ifs
  · change -exponentToInt c (m 1) - (d 1 : ℤ) = -(d 1 : ℤ) - exponentToInt c (m 1)
    ring
  · rw [add_zero]
    rfl

/-- The original left row restriction is the original polynomial-to-Laurent inclusion. -/
theorem twoRowCoordinates_left (d : Fin 2 → ℕ) (b : Fin 3)
    (x : FaceRing R (![b,0] : Fin 2 → Fin 3)) :
    twoRowOneCoordinates R b
      (multiTwistFaceRestriction R (twoRowFaceRefines b 0) (fun v => -(d v : ℤ)) x) =
      CechLine.leftRestriction (TwoRowBase R b) (twoRowFaceCoordinates R b 0 x) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero =>
    rw [(multiTwistFaceRestriction R _ _).map_zero,(twoRowOneCoordinates R b).map_zero,
      (twoRowFaceCoordinates R b 0).map_zero,(CechLine.leftRestriction (TwoRowBase R b)).map_zero]
  | add x y hx hy =>
    rw [(multiTwistFaceRestriction R _ _).map_add,(twoRowOneCoordinates R b).map_add,
      (twoRowFaceCoordinates R b 0).map_add,(CechLine.leftRestriction (TwoRowBase R b)).map_add,hx,hy]
  | single m r =>
    rw [multiTwistFaceRestriction_single]
    change twoRowFaceCoordinates R b 2 _ = _
    rw [twoRowFaceCoordinates_single,twoRowFaceCoordinates_single,
      row_refinement_first,row_refinement_second]
    simp [CechLine.leftRestriction,exponentToInt]
    rfl

/-- The original right row restriction retains the original twist shift minus d(1). -/
theorem twoRowCoordinates_right (d : Fin 2 → ℕ) (b : Fin 3)
    (x : FaceRing R (![b,1] : Fin 2 → Fin 3)) :
    twoRowOneCoordinates R b
      (multiTwistFaceRestriction R (twoRowFaceRefines b 1) (fun v => -(d v : ℤ)) x) =
      CechLine.rightRestriction (TwoRowBase R b) (d 1) (twoRowFaceCoordinates R b 1 x) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero =>
    rw [(multiTwistFaceRestriction R _ _).map_zero,(twoRowOneCoordinates R b).map_zero,
      (twoRowFaceCoordinates R b 1).map_zero,(CechLine.rightRestriction (TwoRowBase R b) (d 1)).map_zero]
  | add x y hx hy =>
    rw [(multiTwistFaceRestriction R _ _).map_add,(twoRowOneCoordinates R b).map_add,
      (twoRowFaceCoordinates R b 1).map_add,(CechLine.rightRestriction (TwoRowBase R b) (d 1)).map_add,hx,hy]
  | single m r =>
    rw [multiTwistFaceRestriction_single]
    change twoRowFaceCoordinates R b 2 _ = _
    rw [twoRowFaceCoordinates_single,twoRowFaceCoordinates_single,
      row_refinement_first,row_refinement_second]
    simp [CechLine.rightRestriction,exponentToInt]
    rfl

/-- The original native row boundary is the negative of the original one-factor Cech differential. -/
theorem twoRowCoordinates_boundary (d : Fin 2 → ℕ) (b : Fin 3)
    (x : FaceRing R (![b,0] : Fin 2 → Fin 3) × FaceRing R (![b,1] : Fin 2 → Fin 3)) :
    twoRowOneCoordinates R b (twoRowBoundary R (fun v => -(d v : ℤ)) b x) =
      -CechLine.differential (TwoRowBase R b) (d 1) (twoRowZeroCoordinates R b x) := by
  calc
    _ = twoRowOneCoordinates R b
        (multiTwistFaceRestriction R (twoRowFaceRefines b 0) (fun v => -(d v : ℤ)) x.1) -
      twoRowOneCoordinates R b
        (multiTwistFaceRestriction R (twoRowFaceRefines b 1) (fun v => -(d v : ℤ)) x.2) :=
      (twoRowOneCoordinates R b).map_sub _ _
    _ = _ := by
      rw [twoRowCoordinates_left,twoRowCoordinates_right]
      change CechLine.leftRestriction (TwoRowBase R b) (twoRowFaceCoordinates R b 0 x.1) -
        CechLine.rightRestriction (TwoRowBase R b) (d 1) (twoRowFaceCoordinates R b 1 x.2) =
        -(CechLine.rightRestriction (TwoRowBase R b) (d 1) (twoRowFaceCoordinates R b 1 x.2) -
          CechLine.leftRestriction (TwoRowBase R b) (twoRowFaceCoordinates R b 0 x.1))
      abel

end BPFixedPoints.CechProduct
