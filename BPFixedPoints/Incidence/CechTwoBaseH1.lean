import BPFixedPoints.Incidence.CechTwoRowH1Kernel

/-! # The original first-coordinate section cokernel and its original Laurent states -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R]

/-- The original two first-coordinate coefficient polynomials in the original one-factor Cech module. -/
noncomputable def twoBasePairCoefficients :
    (TwoRowBase R 0 × TwoRowBase R 1) ≃ₗ[R] CechLine.C0 R :=
  (AddMonoidAlgebra.coeffLinearEquiv R).prodCongr (AddMonoidAlgebra.coeffLinearEquiv R)

/-- The original first-coordinate Laurent coefficients in the original one-factor Cech module. -/
noncomputable def twoBaseOverlapCoefficients : TwoRowBase R 2 ≃ₗ[R] CechLine.C1 R :=
  AddMonoidAlgebra.coeffLinearEquiv R

/-- The original left-minus-right restriction difference on first-coordinate coefficients. -/
noncomputable def twoBaseDifference (d : Fin 2 → ℕ) :
    (TwoRowBase R 0 × TwoRowBase R 1) →ₗ[R] TwoRowBase R 2 :=
  (twoRowBaseRestriction R d (b := 0) (c := 2) (Or.inr rfl)).comp (LinearMap.fst R _ _) -
    (twoRowBaseRestriction R d (b := 1) (c := 2) (Or.inr rfl)).comp (LinearMap.snd R _ _)

/-- The original native coefficient difference is the negative of the original first-factor differential. -/
theorem twoBaseDifference_coefficients (d : Fin 2 → ℕ) (x : TwoRowBase R 0 × TwoRowBase R 1) :
    twoBaseOverlapCoefficients R (twoBaseDifference R d x) =
      -CechLine.differential R (d 0) (twoBasePairCoefficients R x) := by
  change AddMonoidAlgebra.coeffLinearEquiv R
    (twoRowBaseRestriction R d (b := 0) (c := 2) (Or.inr rfl) x.1 -
      twoRowBaseRestriction R d (b := 1) (c := 2) (Or.inr rfl) x.2) = _
  rw [map_sub,twoRowBaseRestriction_left,twoRowBaseRestriction_right]
  change CechLine.leftRestriction R (AddMonoidAlgebra.coeffLinearEquiv R x.1) -
    CechLine.rightRestriction R (d 0) (AddMonoidAlgebra.coeffLinearEquiv R x.2) =
      -(CechLine.rightRestriction R (d 0) (AddMonoidAlgebra.coeffLinearEquiv R x.2) -
        CechLine.leftRestriction R (AddMonoidAlgebra.coeffLinearEquiv R x.1))
  abel

/-- The original first-factor Laurent projection on the original overlap coefficients. -/
noncomputable def twoBaseStateProjection (d : Fin 2 → ℕ) : TwoRowBase R 2 →ₗ[R] CechLine.H1 R (d 0) :=
  (CechLine.projectionOne R (d 0)).comp (twoBaseOverlapCoefficients R).toLinearMap

/-- The original Laurent inclusion supplies every first-factor state. -/
theorem twoBaseStateProjection_surjective (d : Fin 2 → ℕ) :
    Function.Surjective (twoBaseStateProjection R d) := by
  intro s
  refine ⟨(twoBaseOverlapCoefficients R).symm (CechLine.inclusionOne R (d 0) s),?_⟩
  change CechLine.projectionOne R (d 0)
    (twoBaseOverlapCoefficients R ((twoBaseOverlapCoefficients R).symm _)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun (CechLine.projectionOne_inclusionOne R (d 0)) s

/-- The original first-factor section boundaries are precisely the original Laurent projection kernel. -/
theorem twoBaseDifference_range (d : Fin 2 → ℕ) :
    LinearMap.range (twoBaseDifference R d) = LinearMap.ker (twoBaseStateProjection R d) := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    change CechLine.projectionOne R (d 0) (twoBaseOverlapCoefficients R (twoBaseDifference R d x)) = 0
    rw [twoBaseDifference_coefficients,map_neg]
    have he := LinearMap.congr_fun (CechLine.projectionOne_differential R (d 0)) (twoBasePairCoefficients R x)
    exact (congrArg Neg.neg he).trans neg_zero
  · intro hz
    change CechLine.projectionOne R (d 0) (twoBaseOverlapCoefficients R z) = 0 at hz
    refine ⟨(twoBasePairCoefficients R).symm (-(CechLine.homotopy R (d 0) (twoBaseOverlapCoefficients R z))),?_⟩
    apply (twoBaseOverlapCoefficients R).injective
    rw [twoBaseDifference_coefficients,LinearEquiv.apply_symm_apply,map_neg,neg_neg]
    have he := LinearMap.congr_fun (CechLine.differential_homotopy R (d 0)) (twoBaseOverlapCoefficients R z)
    change CechLine.differential R (d 0) (CechLine.homotopy R (d 0) _) =
      twoBaseOverlapCoefficients R z - CechLine.inclusionOne R (d 0)
        (CechLine.projectionOne R (d 0) (twoBaseOverlapCoefficients R z)) at he
    simpa only [hz,map_zero,sub_zero] using he

/-- The original first-coordinate section cokernel equals the original first-factor Laurent state module. -/
noncomputable def twoBaseQuotientStateEquiv (d : Fin 2 → ℕ) :
    (TwoRowBase R 2 ⧸ LinearMap.range (twoBaseDifference R d)) ≃ₗ[R] CechLine.H1 R (d 0) :=
  (Submodule.quotEquivOfEq _ _ (twoBaseDifference_range R d)).trans
    ((twoBaseStateProjection R d).quotKerEquivOfSurjective (twoBaseStateProjection_surjective R d))

/-- Every original first-coordinate coefficient representative retains its original Laurent projection. -/
theorem twoBaseQuotientStateEquiv_mk (d : Fin 2 → ℕ) (z : TwoRowBase R 2) :
    twoBaseQuotientStateEquiv R d (Submodule.Quotient.mk z) = twoBaseStateProjection R d z := rfl

/-- Every original first-factor state keeps its original Laurent inclusion as an inverse representative. -/
theorem twoBaseQuotientStateEquiv_symm (d : Fin 2 → ℕ) (s : CechLine.H1 R (d 0)) :
    (twoBaseQuotientStateEquiv R d).symm s =
      Submodule.Quotient.mk ((twoBaseOverlapCoefficients R).symm (CechLine.inclusionOne R (d 0) s)) := by
  apply (twoBaseQuotientStateEquiv R d).injective
  rw [LinearEquiv.apply_symm_apply,twoBaseQuotientStateEquiv_mk]
  change s = CechLine.projectionOne R (d 0)
    (twoBaseOverlapCoefficients R ((twoBaseOverlapCoefficients R).symm _))
  rw [LinearEquiv.apply_symm_apply]
  exact (LinearMap.congr_fun (CechLine.projectionOne_inclusionOne R (d 0)) s).symm

end BPFixedPoints.CechProduct
