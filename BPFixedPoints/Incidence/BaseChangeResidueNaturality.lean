import BPFixedPoints.Incidence.GradedBaseChangeSpecialization

/-! # Naturality of actual specialization under coefficient homomorphisms -/

namespace BPFixedPoints.ResolutionTools
open MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

variable {k σ R R' J M : Type*} [Field k] [CommRing R] [CommRing R']
  [Algebra k R] [Algebra k R']
  [Algebra (MvPolynomial σ k) R] [Algebra (MvPolynomial σ k) R']
  [IsScalarTower k (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) R']
  [AddCommGroup M] [Module (MvPolynomial σ k) M] [Module k M]
  [IsScalarTower k (MvPolynomial σ k) M]

/-- The actual coefficient map on a free term. -/
noncomputable def coefficientTermMap (φ : R →ₐ[MvPolynomial σ k] R') :
    R ⊗[MvPolynomial σ k] M →ₗ[k] R' ⊗[MvPolynomial σ k] M :=
  (TensorProduct.map φ.toLinearMap LinearMap.id).restrictScalars k

@[simp] theorem coefficientTermMap_tmul (φ : R →ₐ[MvPolynomial σ k] R') (r : R) (x : M) :
    coefficientTermMap φ (r ⊗ₜ[MvPolynomial σ k] x) = φ r ⊗ₜ[MvPolynomial σ k] x := rfl

/-- Residue specialization commutes with the actual coefficient map, in every basis. -/
theorem baseChangeFreeToResidue_natural (φ : R →ₐ[MvPolynomial σ k] R')
    (e : R →+* k) (he : e.comp (algebraMap (MvPolynomial σ k) R) = constantCoeff)
    (e' : R' →+* k) (he' : e'.comp (algebraMap (MvPolynomial σ k) R') = constantCoeff)
    (hφ : e'.comp φ.toRingHom = e) (b : Module.Basis J (MvPolynomial σ k) M)
    (x : R ⊗[MvPolynomial σ k] M) :
    baseChangeFreeToResidue e' he' b (coefficientTermMap φ x) =
      baseChangeFreeToResidue e he b x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
      ext j
      simp only [coefficientTermMap_tmul, baseChangeFreeToResidue, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply, freeResidueMap_apply,
        Module.Basis.baseChange_repr_tmul, Algebra.smul_def, map_mul]
      exact congrArg₂ (· * ·)
        ((DFunLike.congr_fun he' (b.repr x j)).trans (DFunLike.congr_fun he (b.repr x j)).symm)
        (DFunLike.congr_fun hφ r)
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end BPFixedPoints.ResolutionTools
