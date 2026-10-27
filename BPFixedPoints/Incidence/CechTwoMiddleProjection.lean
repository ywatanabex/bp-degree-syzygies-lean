import BPFixedPoints.Incidence.CechProjectionMonomials
import BPFixedPoints.Incidence.CechTwoMiddleStatePiece

/-! # Original full middle cocycles and their specified original row-state projection -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000
variable (R : Type) [CommRing R]

/-- The degree-one cocycles of the original full two-vertex coefficient complex. -/
noncomputable def twoMiddleCycles (d : Fin 2 → ℕ) : Submodule R (C R (Fin 2)) :=
  supported R R {b | (cechDegree b : ℤ) = 1} ⊓ LinearMap.ker (contraction R d).d

/-- The original full state projection, with its original degree-one codomain. -/
noncomputable def twoMiddleStateProjection (d : Fin 2 → ℕ) :
    twoMiddleCycles R d →ₗ[R] twoMiddleStatePiece R d :=
  ((contraction R d).p.comp (twoMiddleCycles R d).subtype).codRestrict _ fun c => by
    change (contraction R d).p c.val ∈ supported R R {_κ : HBasis d | (cohomologyDegree d : ℤ) = 1}
    simpa only [add_zero] using contraction_p_degree R d 1 c.val c.property.1

/-- The original Laurent projections on the two original row-overlap components. -/
noncomputable def twoMiddleRowStates (d : Fin 2 → ℕ) : C R (Fin 2) →ₗ[R]
    CechLine.H1 (TwoRowBase R 0) (d 1) × CechLine.H1 (TwoRowBase R 1) (d 1) :=
  ((twoRowStateProjection R d 0).comp ((LinearMap.proj ![0,2]).comp (faceEquiv R).toLinearMap)).prod
    ((twoRowStateProjection R d 1).comp ((LinearMap.proj ![1,2]).comp (faceEquiv R).toLinearMap))

/-- Every original full middle cocycle satisfies the original rectangular matching equation. -/
theorem twoMiddleCycles_rectangle_closed (d : Fin 2 → ℕ) (c : twoMiddleCycles R d) :
    twoRectangleBoundary R (fun v => -(d v : ℤ)) (twoRectangleComponents R (faceEquiv R c.val)) = 0 := by
  have he := cubicalCoefficientD_two_top R (fun v => -(d v : ℤ)) (faceEquiv R c.val)
  rw [← faceEquiv_d,c.property.2,map_zero] at he
  change 0 = (-twoRectangleOrientation R) • _ at he
  have hs : (-twoRectangleOrientation R)*(-twoRectangleOrientation R) = 1 := by
    rw [neg_mul_neg,twoRectangleOrientation_sq]
  have hh := congrArg (fun z : FaceRing R twoTopFace => (-twoRectangleOrientation R) • z) he
  rw [smul_zero,smul_smul,hs,one_smul] at hh
  exact hh.symm

/-- The original row-state index specifies exactly the original mixed monomial read by the full projection. -/
theorem twoMiddleIndex_projection_monomial (d : Fin 2 → ℕ) (hd : 0 < d 1)
    (k : Fin (d 1-1)) (j : CechLine.H0Index (d 0)) :
    stateProjectionMonomial d ((twoRowMiddleIndexEquiv d hd) (k,j)).val =
      embedFace (![1,2] : Fin 2 → Fin 3) ((twoRowExponentEquiv 1 2).symm (-(k : ℤ)-1,0)) := by
  have h0 : d 0 = 0 := by
    by_contra h0
    have hj := j.isLt
    simp only [ite_eq_right h0] at hj
    omega
  have h1 : (((twoRowMiddleIndexEquiv d hd) (k,j)).val 1).val = k.val := by
    rw [twoRowMiddleIndexEquiv,dite_eq_left h0]
    rfl
  funext v
  fin_cases v
  · change lineProjectionMonomial (d 0) (((twoRowMiddleIndexEquiv d hd) (k,j)).val 0) = _
    have hz (n : ℕ) (hn : n = 0) (a : Fin (phi n)) : lineProjectionMonomial n a = Sum.inr (Sum.inl 0) := by
      subst n
      exact lineProjectionMonomial_zero a
    rw [hz _ h0]
    rfl
  · change lineProjectionMonomial (d 1) (((twoRowMiddleIndexEquiv d hd) (k,j)).val 1) = _
    rw [lineProjectionMonomial_pos _ hd]
    exact congrArg (fun n : ℕ => (Sum.inr (Sum.inr (-(n : ℤ)-1)) : Basis)) h1

/-- The specified row-kernel state of every original full middle cocycle is exactly its original full contraction projection. -/
theorem twoMiddleRowStates_projection (d : Fin 2 → ℕ) (hd : 0 < d 1)
    (c : twoMiddleCycles R d) (z : LinearMap.ker (twoRowStateDifference R d))
    (hz : z.val = twoMiddleRowStates R d c.val) :
    twoRowKernelMiddleStateEquiv R d hd z = twoMiddleStateProjection R d c := by
  apply (supportedEquivFinsupp (R := R) (M := R) {_κ : HBasis d | (cohomologyDegree d : ℤ) = 1}).injective
  apply Finsupp.ext
  intro κ
  obtain ⟨⟨k,j⟩,rfl⟩ := (twoRowMiddleIndexEquiv d hd).surjective κ
  change (supportedEquivFinsupp (R := R) (M := R) _)
    ((supportedEquivFinsupp (R := R) (M := R) _).symm
      (mapDomain (twoRowMiddleIndexEquiv d hd) ((twoRowKernelH0Equiv R d z).uncurry)))
        ((twoRowMiddleIndexEquiv d hd) (k,j)) = _
  rw [LinearEquiv.apply_symm_apply]
  change (mapDomain (twoRowMiddleIndexEquiv d hd) ((twoRowKernelH0Equiv R d z).uncurry))
    ((twoRowMiddleIndexEquiv d hd) (k,j)) =
    (contraction R d).p c.val ((twoRowMiddleIndexEquiv d hd) (k,j)).val
  rw [mapDomain_equiv_apply,Equiv.symm_apply_apply]
  change twoRowKernelH0Equiv R d z k j = (contraction R d).p c.val ((twoRowMiddleIndexEquiv d hd) (k,j)).val
  rw [twoRowKernelH0Equiv_apply,CechLine.projectionZero_apply]
  change (z.val.2 k).coeff 0 = _
  rw [hz]
  change (CechLine.projectionOne (TwoRowBase R 1) (d 1)
    (twoRowOneCoordinates R 1 (faceEquiv R c.val ![1,2])) k).coeff 0 = _
  rw [CechLine.projectionOne_apply]
  change (twoRowFaceCoordinates R 1 2 (faceEquiv R c.val ![1,2]) (-(k : ℤ)-1)).coeff 0 = _
  rw [twoRowFaceCoordinates_coefficient,faceEquiv_coeff,contraction_p_coefficient,
    twoMiddleIndex_projection_monomial]

end BPFixedPoints.CechProduct
