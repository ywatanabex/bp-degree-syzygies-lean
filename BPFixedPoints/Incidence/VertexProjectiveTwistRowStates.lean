import BPFixedPoints.Incidence.CechTwoRowStates
import BPFixedPoints.Incidence.VertexProjectiveTwistRowRestriction

/-! # Actual row H1 and the original one-factor Laurent states -/

namespace BPFixedPoints.CechProduct
open Finsupp
variable (R : Type) [CommRing R]

/-- Read original row states as the original pair of state and first-coordinate monomial indices. -/
noncomputable def twoRowStateBasisEquiv (d : Fin 2 → ℕ) (b : Fin 3) :
    CechLine.H1 (TwoRowBase R b) (d 1) ≃ₗ[R] (Fin (d 1-1) × FaceExponent b) →₀ R :=
  (Finsupp.mapRange.linearEquiv (AddMonoidAlgebra.coeffLinearEquiv R)).trans
    (Finsupp.curryLinearEquiv R).symm

/-- The specified first-direction map on row states uses the original Laurent inclusion and original restriction. -/
noncomputable def twoRowStateRestriction (d : Fin 2 → ℕ) {b c : Fin 3} (h : b = c ∨ c = 2) :
    CechLine.H1 (TwoRowBase R b) (d 1) →ₗ[R] CechLine.H1 (TwoRowBase R c) (d 1) :=
  (twoRowStateProjection R d c).comp
    ((twoRowRestriction R (fun v => -(d v : ℤ)) h 2).comp
      ((twoRowOneCoordinates R b).symm.toLinearMap.comp
        ((CechLine.inclusionOne (TwoRowBase R b) (d 1)).restrictScalars R)))

end BPFixedPoints.CechProduct

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Finsupp TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R] [IsNoetherianRing R]
noncomputable local instance vertexRowStatesHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 2))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Actual row H1 is its original one-factor state module over the independently defined geometric base action. -/
noncomputable def vertexTwistRowStateLinearEquiv (d : Fin 2 → ℕ) (b : Fin 3) :
    vertexTwistRowH1Module R (fun v => -(d v : ℤ)) b ≃ₗ[R] CechLine.H1 (TwoRowBase R b) (d 1) :=
  (vertexTwistRowCoefficientH1LinearEquiv R (fun v => -(d v : ℤ)) b).symm.trans
    (twoRowQuotientStateEquiv R d b)

/-- Every original row connecting representative keeps its original one-factor Laurent projection. -/
theorem vertexTwistRowStateLinearEquiv_representative (d : Fin 2 → ℕ) (b : Fin 3)
    (x : FaceRing R (![b,2] : Fin 2 → Fin 3)) :
    vertexTwistRowStateLinearEquiv R d b
      (vertexTwistRowCoefficientH1LinearEquiv R (fun v => -(d v : ℤ)) b (Submodule.Quotient.mk x)) =
        twoRowStateProjection R d b x := by
  change twoRowQuotientStateEquiv R d b
    ((vertexTwistRowCoefficientH1LinearEquiv R (fun v => -(d v : ℤ)) b).symm
      (vertexTwistRowCoefficientH1LinearEquiv R (fun v => -(d v : ℤ)) b (Submodule.Quotient.mk x))) = _
  rw [LinearEquiv.symm_apply_apply,twoRowQuotientStateEquiv_mk]

/-- Each actual original gap-monomial connecting class has its specified original basis state. -/
theorem vertexTwistRowStateLinearEquiv_gap (d : Fin 2 → ℕ) (b : Fin 3)
    (k : Fin (d 1-1)) (m : FaceExponent b) (r : R) :
    vertexTwistRowStateLinearEquiv R d b
      (vertexTwistRowCoefficientH1LinearEquiv R (fun v => -(d v : ℤ)) b
        (Submodule.Quotient.mk (AddMonoidAlgebra.single (twoRowGapExponent b k m) r))) =
      single k (AddMonoidAlgebra.single m r) := by
  rw [vertexTwistRowStateLinearEquiv_representative,twoRowStateProjection_gap]

/-- The actual inverse row state retains the original Laurent inclusion, original frame and original connecting map. -/
theorem vertexTwistRowStateLinearEquiv_inverse (d : Fin 2 → ℕ) (b : Fin 3)
    (s : CechLine.H1 (TwoRowBase R b) (d 1)) :
    (vertexTwistRowStateLinearEquiv R d b).symm s =
      vertexTwistRowCoefficientH1LinearEquiv R (fun v => -(d v : ℤ)) b
        (Submodule.Quotient.mk ((twoRowOneCoordinates R b).symm
          (CechLine.inclusionOne (TwoRowBase R b) (d 1) s))) := by
  apply (vertexTwistRowStateLinearEquiv R d b).injective
  rw [LinearEquiv.apply_symm_apply,vertexTwistRowStateLinearEquiv_representative]
  change s = CechLine.projectionOne _ _ (twoRowOneCoordinates R b ((twoRowOneCoordinates R b).symm _))
  rw [LinearEquiv.apply_symm_apply]
  exact (LinearMap.congr_fun (CechLine.projectionOne_inclusionOne (TwoRowBase R b) (d 1)) s).symm

/-- Actual first-direction restrictions retain the specified original state inclusion and coefficient maps. -/
theorem vertexTwistRowStateLinearEquiv_restrict_inverse (d : Fin 2 → ℕ) {b c : Fin 3}
    (h : b = c ∨ c = 2) (s : CechLine.H1 (TwoRowBase R b) (d 1)) :
    vertexTwistRowStateLinearEquiv R d c
      (vertexTwistRowH1Restriction R (fun v => -(d v : ℤ)) h
        ((vertexTwistRowStateLinearEquiv R d b).symm s)) = twoRowStateRestriction R d h s := by
  rw [vertexTwistRowStateLinearEquiv_inverse,← vertexTwistRowCoefficientH1LinearEquiv_restrict,
    twoRowQuotientRestriction_mk,vertexTwistRowStateLinearEquiv_representative]
  rfl

/-- The actual row H1 comparison preserves every original first-direction restriction on every class. -/
theorem vertexTwistRowStateLinearEquiv_restrict (d : Fin 2 → ℕ) {b c : Fin 3} (h : b = c ∨ c = 2)
    (x : vertexTwistRowH1Module R (fun v => -(d v : ℤ)) b) :
    vertexTwistRowStateLinearEquiv R d c (vertexTwistRowH1Restriction R (fun v => -(d v : ℤ)) h x) =
      twoRowStateRestriction R d h (vertexTwistRowStateLinearEquiv R d b x) := by
  have he := vertexTwistRowStateLinearEquiv_restrict_inverse R d h (vertexTwistRowStateLinearEquiv R d b x)
  rw [LinearEquiv.symm_apply_apply] at he
  exact he

/-- The original state and first-coordinate monomials are a free original-base basis of actual row H1. -/
noncomputable def vertexTwistRowH1BasisLinearEquiv (d : Fin 2 → ℕ) (b : Fin 3) :
    vertexTwistRowH1Module R (fun v => -(d v : ℤ)) b ≃ₗ[R] (Fin (d 1-1) × FaceExponent b) →₀ R :=
  (vertexTwistRowStateLinearEquiv R d b).trans (twoRowStateBasisEquiv R d b)

/-- Actual row H1 is free over the original base, with no field or domain assumption. -/
theorem vertexTwistRowH1_free (d : Fin 2 → ℕ) (b : Fin 3) :
    Module.Free R (vertexTwistRowH1Module R (fun v => -(d v : ℤ)) b) :=
  Module.Free.of_equiv (vertexTwistRowH1BasisLinearEquiv R d b).symm

/-- A second-direction twist parameter zero or one has no original row H1 states. -/
theorem vertexTwistRowH1_eq_zero_of_le_one (d : Fin 2 → ℕ) (b : Fin 3) (hd : d 1 ≤ 1)
    (x : vertexTwistRowH1Module R (fun v => -(d v : ℤ)) b) : x = 0 := by
  apply (vertexTwistRowStateLinearEquiv R d b).injective
  rw [map_zero]
  apply Finsupp.ext
  intro k
  have hk := k.isLt
  omega

end BPFixedPoints.ProjectiveLine
