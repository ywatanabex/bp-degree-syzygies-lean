import BPFixedPoints.Incidence.CechTwoMiddleProjection
import BPFixedPoints.Incidence.VertexProjectiveTwistRowH0Restriction

/-! # Original row primitives for zero second twist -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
variable (R : Type) [CommRing R]

/-- The original row homotopy, with the native left-minus-right boundary convention. -/
noncomputable def twoRowPrimitive (d : Fin 2 → ℕ) (b : Fin 3) :
    FaceRing R (![b,2] : Fin 2 → Fin 3) →ₗ[R]
      (FaceRing R (![b,0] : Fin 2 → Fin 3) × FaceRing R (![b,1] : Fin 2 → Fin 3)) :=
  (twoRowZeroCoordinates R b).symm.toLinearMap.comp
    ((-(CechLine.homotopy (TwoRowBase R b) (d 1)).restrictScalars R).comp
      (twoRowOneCoordinates R b).toLinearMap)

/-- Every original row-overlap coefficient is the native boundary of its original primitive when the second twist is zero. -/
theorem twoRowPrimitive_boundary (d : Fin 2 → ℕ) (hd : d 1 = 0) (b : Fin 3)
    (x : FaceRing R (![b,2] : Fin 2 → Fin 3)) :
    twoRowBoundary R (fun v => -(d v : ℤ)) b (twoRowPrimitive R d b x) = x := by
  apply (twoRowOneCoordinates R b).injective
  rw [twoRowCoordinates_boundary]
  change -CechLine.differential (TwoRowBase R b) (d 1)
    (twoRowZeroCoordinates R b ((twoRowZeroCoordinates R b).symm
      (-CechLine.homotopy (TwoRowBase R b) (d 1) (twoRowOneCoordinates R b x)))) = _
  rw [LinearEquiv.apply_symm_apply,map_neg,neg_neg]
  have hp : CechLine.projectionOne (TwoRowBase R b) (d 1) (twoRowOneCoordinates R b x) = 0 := by
    apply Finsupp.ext
    intro k
    have hk := k.isLt
    change k.val < d 1-1 at hk
    omega
  have he := LinearMap.congr_fun (CechLine.differential_homotopy (TwoRowBase R b) (d 1))
    (twoRowOneCoordinates R b x)
  change CechLine.differential _ _ (CechLine.homotopy _ _ _) =
    twoRowOneCoordinates R b x - CechLine.inclusionOne _ _ (CechLine.projectionOne _ _ _) at he
  simpa only [hp,map_zero,sub_zero] using he

/-- The original primitive has zero right-chart constant coefficient, without any choice of a splitting. -/
theorem twoRowPrimitive_right_constant (d : Fin 2 → ℕ) (hd : d 1 = 0) (b : Fin 3)
    (x : FaceRing R (![b,2] : Fin 2 → Fin 3)) :
    twoRowFaceCoordinates R b 1 (twoRowPrimitive R d b x).2 0 = 0 := by
  have he := LinearMap.congr_fun (CechLine.projectionZero_homotopy (TwoRowBase R b) (d 1))
    (twoRowOneCoordinates R b x)
  let k : CechLine.H0Index (d 1) := ⟨0,by simp [hd]⟩
  have hk := congrArg (fun z : CechLine.H0 (TwoRowBase R b) (d 1) => z k) he
  change CechLine.projectionZero (TwoRowBase R b) (d 1)
    (CechLine.homotopy (TwoRowBase R b) (d 1) (twoRowOneCoordinates R b x)) k = 0 at hk
  rw [CechLine.projectionZero_apply] at hk
  have hc := congrArg (fun z : CechLine.C0 (TwoRowBase R b) => z.2 0)
    ((twoRowZeroCoordinates R b).apply_symm_apply
      (-CechLine.homotopy (TwoRowBase R b) (d 1) (twoRowOneCoordinates R b x)))
  change twoRowFaceCoordinates R b 1 (twoRowPrimitive R d b x).2 0 =
    -(CechLine.homotopy (TwoRowBase R b) (d 1) (twoRowOneCoordinates R b x)).2 0 at hc
  exact hc.trans ((congrArg Neg.neg hk).trans neg_zero)

/-- Apply the original first-direction refinement to both original corners of a row. -/
noncomputable def twoRowCornerRestriction (d : Fin 2 → ℕ) {b c : Fin 3} (h : b = c ∨ c = 2) :
    (FaceRing R (![b,0] : Fin 2 → Fin 3) × FaceRing R (![b,1] : Fin 2 → Fin 3)) →ₗ[R]
      (FaceRing R (![c,0] : Fin 2 → Fin 3) × FaceRing R (![c,1] : Fin 2 → Fin 3)) :=
  (twoRowRestriction R (fun v => -(d v : ℤ)) h 0).prodMap
    (twoRowRestriction R (fun v => -(d v : ℤ)) h 1)

/-- Original corner refinements commute with the original native row boundary. -/
theorem twoRowCornerRestriction_boundary (d : Fin 2 → ℕ) {b c : Fin 3} (h : b = c ∨ c = 2)
    (x : FaceRing R (![b,0] : Fin 2 → Fin 3) × FaceRing R (![b,1] : Fin 2 → Fin 3)) :
    twoRowBoundary R (fun v => -(d v : ℤ)) c (twoRowCornerRestriction R d h x) =
      twoRowRestriction R (fun v => -(d v : ℤ)) h 2 (twoRowBoundary R (fun v => -(d v : ℤ)) b x) :=
  (twoRowRestriction_boundary R _ h x).symm

end BPFixedPoints.CechProduct
