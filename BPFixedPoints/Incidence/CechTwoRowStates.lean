import BPFixedPoints.Incidence.CechTwoRowCoordinates

/-! # The original one-factor state projection on every original two-coordinate row -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 600000
variable (R : Type) [CommRing R]

/-- The original one-factor Laurent projection with its original first-coordinate coefficients. -/
noncomputable def twoRowStateProjection (d : Fin 2 → ℕ) (b : Fin 3) :
    FaceRing R (![b,2] : Fin 2 → Fin 3) →ₗ[R] CechLine.H1 (TwoRowBase R b) (d 1) :=
  ((CechLine.projectionOne (TwoRowBase R b) (d 1)).restrictScalars R).comp
    (twoRowOneCoordinates R b).toLinearMap

/-- The original inclusion supplies every row state without splitting a surjection over the base ring. -/
theorem twoRowStateProjection_surjective (d : Fin 2 → ℕ) (b : Fin 3) :
    Function.Surjective (twoRowStateProjection R d b) := by
  intro s
  refine ⟨(twoRowOneCoordinates R b).symm (CechLine.inclusionOne (TwoRowBase R b) (d 1) s),?_⟩
  change CechLine.projectionOne _ _ (twoRowOneCoordinates R b ((twoRowOneCoordinates R b).symm _)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun (CechLine.projectionOne_inclusionOne (TwoRowBase R b) (d 1)) s

/-- The original row boundary image is exactly the original Laurent state-projection kernel. -/
theorem twoRowBoundary_range_state (d : Fin 2 → ℕ) (b : Fin 3) :
    LinearMap.range (twoRowBoundary R (fun v => -(d v : ℤ)) b) =
      LinearMap.ker (twoRowStateProjection R d b) := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    change CechLine.projectionOne _ _ (twoRowOneCoordinates R b (twoRowBoundary R _ b x)) = 0
    rw [twoRowCoordinates_boundary,(CechLine.projectionOne (TwoRowBase R b) (d 1)).map_neg]
    have he := LinearMap.congr_fun (CechLine.projectionOne_differential (TwoRowBase R b) (d 1))
      (twoRowZeroCoordinates R b x)
    exact (congrArg Neg.neg he).trans neg_zero
  · intro hz
    change CechLine.projectionOne (TwoRowBase R b) (d 1) (twoRowOneCoordinates R b z) = 0 at hz
    refine ⟨(twoRowZeroCoordinates R b).symm
      (-(CechLine.homotopy (TwoRowBase R b) (d 1) (twoRowOneCoordinates R b z))),?_⟩
    apply (twoRowOneCoordinates R b).injective
    rw [twoRowCoordinates_boundary,LinearEquiv.apply_symm_apply,
      (CechLine.differential (TwoRowBase R b) (d 1)).map_neg,neg_neg]
    have he := LinearMap.congr_fun (CechLine.differential_homotopy (TwoRowBase R b) (d 1))
      (twoRowOneCoordinates R b z)
    change CechLine.differential _ _ (CechLine.homotopy _ _ _) =
      twoRowOneCoordinates R b z - CechLine.inclusionOne _ _
        (CechLine.projectionOne _ _ (twoRowOneCoordinates R b z)) at he
    simpa only [hz,map_zero,sub_zero] using he

/-- Every original row coefficient quotient equals its original one-factor state module linearly over the original base. -/
noncomputable def twoRowQuotientStateEquiv (d : Fin 2 → ℕ) (b : Fin 3) :
    (FaceRing R (![b,2] : Fin 2 → Fin 3) ⧸ LinearMap.range (twoRowBoundary R (fun v => -(d v : ℤ)) b)) ≃ₗ[R]
      CechLine.H1 (TwoRowBase R b) (d 1) :=
  (Submodule.quotEquivOfEq _ _ (twoRowBoundary_range_state R d b)).trans
    ((twoRowStateProjection R d b).quotKerEquivOfSurjective (twoRowStateProjection_surjective R d b))

/-- Every original row quotient representative retains the original Laurent projection. -/
theorem twoRowQuotientStateEquiv_mk (d : Fin 2 → ℕ) (b : Fin 3)
    (x : FaceRing R (![b,2] : Fin 2 → Fin 3)) :
    twoRowQuotientStateEquiv R d b (Submodule.Quotient.mk x) = twoRowStateProjection R d b x := rfl

/-- Every original row state has its original Laurent inclusion as its specified inverse representative. -/
theorem twoRowQuotientStateEquiv_symm (d : Fin 2 → ℕ) (b : Fin 3)
    (s : CechLine.H1 (TwoRowBase R b) (d 1)) :
    (twoRowQuotientStateEquiv R d b).symm s =
      Submodule.Quotient.mk ((twoRowOneCoordinates R b).symm
        (CechLine.inclusionOne (TwoRowBase R b) (d 1) s)) := by
  apply (twoRowQuotientStateEquiv R d b).injective
  rw [LinearEquiv.apply_symm_apply,twoRowQuotientStateEquiv_mk]
  change s = CechLine.projectionOne _ _ (twoRowOneCoordinates R b ((twoRowOneCoordinates R b).symm _))
  rw [LinearEquiv.apply_symm_apply]
  exact (LinearMap.congr_fun (CechLine.projectionOne_inclusionOne (TwoRowBase R b) (d 1)) s).symm

/-- The original mixed monomial has its prescribed first exponent and original one-factor gap exponent. -/
def twoRowGapExponent (b : Fin 3) (k : ℕ) (m : FaceExponent b) :
    FaceMonoid (![b,2] : Fin 2 → Fin 3) :=
  (twoRowExponentEquiv b 2).symm (-(k : ℤ)-1,m)

/-- Every original row basis representative projects to its original state and first-coordinate coefficient. -/
theorem twoRowStateProjection_gap (d : Fin 2 → ℕ) (b : Fin 3)
    (k : Fin (d 1-1)) (m : FaceExponent b) (r : R) :
    twoRowStateProjection R d b (AddMonoidAlgebra.single (twoRowGapExponent b k m) r) =
      single k (AddMonoidAlgebra.single m r) := by
  have he : twoRowOneCoordinates R b (AddMonoidAlgebra.single (twoRowGapExponent b k m) r) =
      CechLine.inclusionOne (TwoRowBase R b) (d 1) (single k (AddMonoidAlgebra.single m r)) := by
    change twoRowFaceCoordinates R b 2 _ = _
    rw [twoRowFaceCoordinates_single,CechLine.inclusionOne_single]
    have h := (twoRowExponentEquiv b 2).apply_symm_apply (-(k : ℤ)-1,m)
    change ((twoRowGapExponent b k m) 1,(twoRowGapExponent b k m) 0) = (-(k : ℤ)-1,m) at h
    rw [(Prod.mk.inj h).1,(Prod.mk.inj h).2]
  change CechLine.projectionOne _ _ (twoRowOneCoordinates R b _) = _
  rw [he]
  exact LinearMap.congr_fun (CechLine.projectionOne_inclusionOne (TwoRowBase R b) (d 1)) _

end BPFixedPoints.CechProduct
