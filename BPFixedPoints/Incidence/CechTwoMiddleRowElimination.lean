import BPFixedPoints.Incidence.CechTwoRowPrimitives

/-! # Original row elimination on full middle cocycles -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
variable (R : Type) [CommRing R]

/-- Take the original primitive of an original row-overlap component of the full complex. -/
noncomputable def twoMiddleRowPrimitive (d : Fin 2 → ℕ) (b : Fin 3) :
    C R (Fin 2) →ₗ[R]
      (FaceRing R (![b,0] : Fin 2 → Fin 3) × FaceRing R (![b,1] : Fin 2 → Fin 3)) :=
  (twoRowPrimitive R d b).comp ((LinearMap.proj ![b,2]).comp (faceEquiv R).toLinearMap)

/-- Eliminate the original row-overlap components using their original row primitives. -/
noncomputable def twoMiddleCorrectedCorners (d : Fin 2 → ℕ) :
    C R (Fin 2) →ₗ[R]
      (FaceRing R (![2,0] : Fin 2 → Fin 3) × FaceRing R (![2,1] : Fin 2 → Fin 3)) :=
  (((LinearMap.proj ![2,0]).prod (LinearMap.proj ![2,1])).comp (faceEquiv R).toLinearMap) -
    (((twoRowCornerRestriction R d (b := 0) (c := 2) (Or.inr rfl)).comp (twoMiddleRowPrimitive R d 0)) -
      ((twoRowCornerRestriction R d (b := 1) (c := 2) (Or.inr rfl)).comp (twoMiddleRowPrimitive R d 1)))

/-- Rectangular closedness makes the corrected original corner coefficients match on their original overlap. -/
theorem twoMiddleCorrectedCorners_closed (d : Fin 2 → ℕ) (hd : d 1 = 0) (c : twoMiddleCycles R d) :
    twoRowBoundary R (fun v => -(d v : ℤ)) 2 (twoMiddleCorrectedCorners R d c.val) = 0 := by
  change twoRowBoundary R (fun v => -(d v : ℤ)) 2
    ((faceEquiv R c.val ![2,0],faceEquiv R c.val ![2,1]) -
      (twoRowCornerRestriction R d (b := 0) (c := 2) (Or.inr rfl)
        (twoRowPrimitive R d 0 (faceEquiv R c.val ![0,2])) -
       twoRowCornerRestriction R d (b := 1) (c := 2) (Or.inr rfl)
        (twoRowPrimitive R d 1 (faceEquiv R c.val ![1,2])))) = 0
  rw [map_sub,map_sub,twoRowCornerRestriction_boundary,twoRowCornerRestriction_boundary,
    twoRowPrimitive_boundary R d hd,twoRowPrimitive_boundary R d hd]
  have hc := twoMiddleCycles_rectangle_closed R d c
  exact sub_eq_zero.mpr (sub_eq_zero.mp hc).symm

/-- The corrected corners lie in the original row-section matching kernel. -/
noncomputable def twoMiddleCorrectedKernel (d : Fin 2 → ℕ) (hd : d 1 = 0) :
    twoMiddleCycles R d →ₗ[R] LinearMap.ker (twoRowBoundary R (fun v => -(d v : ℤ)) 2) :=
  ((twoMiddleCorrectedCorners R d).comp (twoMiddleCycles R d).subtype).codRestrict _
    (twoMiddleCorrectedCorners_closed R d hd)

/-- Row elimination preserves the original second right-chart constant coefficient. -/
theorem twoMiddleCorrectedCorners_constant (d : Fin 2 → ℕ) (hd : d 1 = 0) (x : C R (Fin 2)) :
    twoRowFaceCoordinates R 2 1 (twoMiddleCorrectedCorners R d x).2 0 =
      twoRowFaceCoordinates R 2 1 (faceEquiv R x ![2,1]) 0 := by
  change twoRowFaceCoordinates R 2 1
    (faceEquiv R x ![2,1] -
      (twoRowRestriction R (fun v => -(d v : ℤ)) (b := 0) (c := 2) (Or.inr rfl) 1
        (twoRowPrimitive R d 0 (faceEquiv R x ![0,2])).2 -
       twoRowRestriction R (fun v => -(d v : ℤ)) (b := 1) (c := 2) (Or.inr rfl) 1
        (twoRowPrimitive R d 1 (faceEquiv R x ![1,2])).2)) 0 = _
  rw [map_sub,map_sub,twoRowRightCoordinates_restrict,twoRowRightCoordinates_restrict]
  change twoRowFaceCoordinates R 2 1 (faceEquiv R x ![2,1]) 0 -
    (twoRowBaseRestriction R d (b := 0) (c := 2) (Or.inr rfl)
      (twoRowFaceCoordinates R 0 1 (twoRowPrimitive R d 0 (faceEquiv R x ![0,2])).2 0) -
     twoRowBaseRestriction R d (b := 1) (c := 2) (Or.inr rfl)
      (twoRowFaceCoordinates R 1 1 (twoRowPrimitive R d 1 (faceEquiv R x ![1,2])).2 0)) = _
  rw [twoRowPrimitive_right_constant R d hd,twoRowPrimitive_right_constant R d hd,
    (twoRowBaseRestriction R d (b := 0) (c := 2) (Or.inr rfl)).map_zero,
    (twoRowBaseRestriction R d (b := 1) (c := 2) (Or.inr rfl)).map_zero,sub_self,sub_zero]

end BPFixedPoints.CechProduct
