import BPFixedPoints.Incidence.VertexProjectiveTwistRowStates

/-! # Original first-coordinate monomial formulas on actual row H1 -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 600000
variable (R : Type) [CommRing R]

/-- The original first-coordinate refinement, including the original right-chart twist shift. -/
noncomputable def twoRowFirstExponent (d : Fin 2 → ℕ) {b c : Fin 3}
    (h : b = c ∨ c = 2) (m : FaceExponent b) : FaceExponent c :=
  refinementCoordinate h m + if b = 1 ∧ c = 2 then exponentFromInt c (-(d 0 : ℤ)) else 0

/-- Original row gap monomials retain their second-coordinate gap under first-coordinate restriction. -/
theorem twoRowGapExponent_restrict (d : Fin 2 → ℕ) {b c : Fin 3}
    (h : b = c ∨ c = 2) (k : ℕ) (m : FaceExponent b) :
    refinementExponent (twoColumnFaceRefines h 2) (twoRowGapExponent b k m) +
        twistRestrictionShift (twoColumnFaceRefines h 2) (fun v => -(d v : ℤ)) =
      twoRowGapExponent c k (twoRowFirstExponent d h m) := by
  apply (twoRowExponentEquiv c 2).injective
  change (twoRowExponentEquiv c 2) _ =
    (twoRowExponentEquiv c 2) ((twoRowExponentEquiv c 2).symm _)
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · change faceToInt (![c,2] : Fin 2 → Fin 3)
      (refinementExponent (twoColumnFaceRefines h 2) (twoRowGapExponent b k m) +
        twistRestrictionShift (twoColumnFaceRefines h 2) (fun v => -(d v : ℤ))) 1 = _
    rw [map_add,Pi.add_apply,faceToInt_refinement,faceToInt_twistRestrictionShift]
    simp only [Matrix.cons_val_one,Matrix.cons_val_zero,show (2 : Fin 3) ≠ 1 by decide,
      false_and,ite_false,add_zero]
    rfl
  · rfl

/-- The original inverse Laurent coordinates of a gap basis vector are its original mixed monomial. -/
theorem twoRowOneCoordinates_symm_gap (d : Fin 2 → ℕ) (b : Fin 3)
    (k : Fin (d 1-1)) (m : FaceExponent b) (r : R) :
    (twoRowOneCoordinates R b).symm
        (CechLine.inclusionOne (TwoRowBase R b) (d 1) (single k (AddMonoidAlgebra.single m r))) =
      AddMonoidAlgebra.single (twoRowGapExponent b k m) r := by
  apply (twoRowOneCoordinates R b).injective
  rw [LinearEquiv.apply_symm_apply,CechLine.inclusionOne_single]
  change _ = twoRowFaceCoordinates R b 2 _
  rw [twoRowFaceCoordinates_single]
  rfl

/-- Original row restriction acts on its specified Laurent basis by the original first-coordinate monomial map. -/
theorem twoRowStateRestriction_single (d : Fin 2 → ℕ) {b c : Fin 3}
    (h : b = c ∨ c = 2) (k : Fin (d 1-1)) (m : FaceExponent b) (r : R) :
    twoRowStateRestriction R d h (single k (AddMonoidAlgebra.single m r)) =
      single k (AddMonoidAlgebra.single (twoRowFirstExponent d h m) r) := by
  change twoRowStateProjection R d c
    (twoRowRestriction R (fun v => -(d v : ℤ)) h 2
      ((twoRowOneCoordinates R b).symm (CechLine.inclusionOne _ _ _))) = _
  rw [twoRowOneCoordinates_symm_gap]
  change twoRowStateProjection R d c (multiTwistFaceRestriction R _ _ _) = _
  rw [multiTwistFaceRestriction_single,twoRowGapExponent_restrict,twoRowStateProjection_gap]

/-- The left row restriction retains the original nonnegative first exponent. -/
theorem twoRowStateRestriction_left_single (d : Fin 2 → ℕ)
    (k : Fin (d 1-1)) (m : ℕ) (r : R) :
    twoRowStateRestriction R d (b := 0) (c := 2) (Or.inr rfl)
        (single k (AddMonoidAlgebra.single m r)) =
      single k (AddMonoidAlgebra.single (m : ℤ) r) := by
  rw [twoRowStateRestriction_single]
  congr 2

/-- The right row restriction retains the inverse exponent and the original shift minus d(0). -/
theorem twoRowStateRestriction_right_single (d : Fin 2 → ℕ)
    (k : Fin (d 1-1)) (m : ℕ) (r : R) :
    twoRowStateRestriction R d (b := 1) (c := 2) (Or.inr rfl)
        (single k (AddMonoidAlgebra.single m r)) =
      single k (AddMonoidAlgebra.single (-(d 0 : ℤ)-m) r) := by
  rw [twoRowStateRestriction_single]
  congr 2
  simp [twoRowFirstExponent,refinementCoordinate,exponentToInt,exponentFromInt]
  change -(m : ℤ) + -(d 0 : ℤ) = _
  ring

/-- The original first-coordinate coefficient map, with the twist shift fixed before any cohomology comparison. -/
noncomputable def twoRowBaseRestriction (d : Fin 2 → ℕ) {b c : Fin 3} (h : b = c ∨ c = 2) :
    TwoRowBase R b →ₗ[R] TwoRowBase R c :=
  (AddMonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap.comp
    ((Finsupp.lmapDomain R R (twoRowFirstExponent d h)).comp
      (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap)

/-- The original first-coordinate coefficient map on each original monomial. -/
theorem twoRowBaseRestriction_single (d : Fin 2 → ℕ) {b c : Fin 3}
    (h : b = c ∨ c = 2) (m : FaceExponent b) (r : R) :
    twoRowBaseRestriction R d h (AddMonoidAlgebra.single m r) =
      AddMonoidAlgebra.single (twoRowFirstExponent d h m) r := by
  change (AddMonoidAlgebra.coeffLinearEquiv R).symm
    (Finsupp.mapDomain (twoRowFirstExponent d h) (single m r)) = _
  rw [mapDomain_single]
  rfl

/-- Actual row-state restriction is the original coefficient map applied independently at every original gap. -/
theorem twoRowStateRestriction_pointwise (d : Fin 2 → ℕ) {b c : Fin 3}
    (h : b = c ∨ c = 2) (s : CechLine.H1 (TwoRowBase R b) (d 1)) :
    twoRowStateRestriction R d h s = Finsupp.mapRange.linearMap (twoRowBaseRestriction R d h) s := by
  induction s using Finsupp.induction_linear with
  | zero => rw [(twoRowStateRestriction R d h).map_zero,LinearMap.map_zero]
  | add x y hx hy =>
    rw [(twoRowStateRestriction R d h).map_add,LinearMap.map_add,hx,hy]
  | single k a =>
    induction a using AddMonoidAlgebra.induction_linear with
    | zero => rw [single_zero,(twoRowStateRestriction R d h).map_zero,LinearMap.map_zero]
    | add a a' ha ha' =>
      rw [single_add,(twoRowStateRestriction R d h).map_add,LinearMap.map_add,ha,ha']
    | single m r =>
      rw [twoRowStateRestriction_single,Finsupp.mapRange.linearMap_apply,mapRange_single,
        twoRowBaseRestriction_single]

end BPFixedPoints.CechProduct

namespace BPFixedPoints.ProjectiveLine
open CechProduct Finsupp
variable (R : Type) [CommRing R] [IsNoetherianRing R]

/-- The specified actual Ext restriction is the original first-coordinate coefficient map at every Laurent gap. -/
theorem vertexTwistRowStateLinearEquiv_restrict_pointwise (d : Fin 2 → ℕ) {b c : Fin 3}
    (h : b = c ∨ c = 2) (x : vertexTwistRowH1Module R (fun v => -(d v : ℤ)) b) :
    vertexTwistRowStateLinearEquiv R d c (vertexTwistRowH1Restriction R (fun v => -(d v : ℤ)) h x) =
      Finsupp.mapRange.linearMap (twoRowBaseRestriction R d h) (vertexTwistRowStateLinearEquiv R d b x) := by
  rw [vertexTwistRowStateLinearEquiv_restrict,twoRowStateRestriction_pointwise]

end BPFixedPoints.ProjectiveLine
