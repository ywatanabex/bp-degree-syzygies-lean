import BPFixedPoints.Incidence.CechTwoMiddleRowElimination
import BPFixedPoints.Incidence.CechTwoBaseH1

/-! # Original full middle projection with zero second twist -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
variable (R : Type) [CommRing R]

/-- The original first gap and second zero state select the original horizontal-overlap monomial. -/
theorem twoBaseMiddleIndex_projection_monomial (d : Fin 2 → ℕ) (hd : d 1 = 0)
    (k : Fin (d 0-1)) :
    stateProjectionMonomial d ((twoBaseMiddleIndexEquiv d hd) k).val =
      embedFace (![2,1] : Fin 2 → Fin 3) ((twoRowExponentEquiv 2 1).symm (0,-(k : ℤ)-1)) := by
  have h0 : 0 < d 0 := by have hk := k.isLt; omega
  have h1 : (((twoBaseMiddleIndexEquiv d hd) k).val 0).val = k.val := by
    rw [twoBaseMiddleIndexEquiv,dite_eq_left h0]
    rfl
  funext v
  fin_cases v
  · change lineProjectionMonomial (d 0) (((twoBaseMiddleIndexEquiv d hd) k).val 0) = _
    rw [lineProjectionMonomial_pos _ h0]
    exact congrArg (fun n : ℕ => (Sum.inr (Sum.inr (-(n : ℤ)-1)) : Basis)) h1
  · change lineProjectionMonomial (d 1) (((twoBaseMiddleIndexEquiv d hd) k).val 1) = _
    have hz (n : ℕ) (hn : n = 0) (a : Fin (phi n)) : lineProjectionMonomial n a = Sum.inr (Sum.inl 0) := by
      subst n
      exact lineProjectionMonomial_zero a
    rw [hz _ hd]
    rfl

/-- The original horizontal Laurent projection is exactly the original full middle projection. -/
theorem twoMiddleZeroSecond_projection (d : Fin 2 → ℕ) (hd : d 1 = 0)
    (c : twoMiddleCycles R d) (z : TwoRowBase R 2)
    (hz : z = twoRowFaceCoordinates R 2 1 (faceEquiv R c.val ![2,1]) 0) :
    twoBaseH1MiddleStateEquiv R d hd (twoBaseStateProjection R d z) =
      twoMiddleStateProjection R d c := by
  apply (supportedEquivFinsupp (R := R) (M := R) {_κ : HBasis d | (cohomologyDegree d : ℤ) = 1}).injective
  apply Finsupp.ext
  intro κ
  obtain ⟨k,rfl⟩ := (twoBaseMiddleIndexEquiv d hd).surjective κ
  change (supportedEquivFinsupp (R := R) (M := R) _)
    ((supportedEquivFinsupp (R := R) (M := R) _).symm
      (mapDomain (twoBaseMiddleIndexEquiv d hd) (twoBaseStateProjection R d z)))
        ((twoBaseMiddleIndexEquiv d hd) k) = _
  rw [LinearEquiv.apply_symm_apply]
  change (mapDomain (twoBaseMiddleIndexEquiv d hd) (twoBaseStateProjection R d z))
    ((twoBaseMiddleIndexEquiv d hd) k) =
      (contraction R d).p c.val ((twoBaseMiddleIndexEquiv d hd) k).val
  rw [mapDomain_equiv_apply,Equiv.symm_apply_apply]
  change CechLine.projectionOne R (d 0) ((twoBaseOverlapCoefficients R) z) k = _
  rw [CechLine.projectionOne_apply]
  change z.coeff (-(k : ℤ)-1) = _
  rw [hz,twoRowFaceCoordinates_coefficient,faceEquiv_coeff,contraction_p_coefficient,
    twoBaseMiddleIndex_projection_monomial]

end BPFixedPoints.CechProduct
