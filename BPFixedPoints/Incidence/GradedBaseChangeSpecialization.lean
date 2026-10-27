import BPFixedPoints.Incidence.GradedBaseChangeFree

/-! # Specialization of natural shifted pieces after a coefficient cut -/

namespace BPFixedPoints.ResolutionTools

open Finsupp MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k σ R J M : Type*} [Field k] [CommRing R] [Algebra k R]
  [Algebra (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) R]
  (e : R →+* k) (he : e.comp (algebraMap (MvPolynomial σ k) R) = constantCoeff)

/-- A compatible coefficient origin is automatically a ground-field algebra map. -/
def residueAlgHom : R →ₐ[k] k where
  toRingHom := e
  commutes' c := by
    change e (algebraMap k R c) = c
    rw [IsScalarTower.algebraMap_eq k (MvPolynomial σ k) R]
    simpa using DFunLike.congr_fun he (C c)

noncomputable def freeResidueMap : (J →₀ R) →ₗ[k] (J →₀ k) :=
  Finsupp.mapRange.linearMap (residueAlgHom e he).toLinearMap

@[simp] theorem freeResidueMap_apply (x : J →₀ R) (j : J) :
    freeResidueMap e he x j = e (x j) := rfl

variable [AddCommGroup M] [Module (MvPolynomial σ k) M] [Module k M]
  [IsScalarTower k (MvPolynomial σ k) M]
  (b : Module.Basis J (MvPolynomial σ k) M) (w : J → ℕ)

noncomputable def baseChangeFreeToResidue : (R ⊗[MvPolynomial σ k] M) →ₗ[k] (J →₀ k) :=
  (freeResidueMap e he).comp ((b.baseChange R).repr.restrictScalars k).toLinearMap

@[simp] theorem baseChangeFreeToResidue_unit (x : M) :
    baseChangeFreeToResidue e he b (baseChangeUnit (R := R) x) = freeAtOrigin (b.repr x) := by
  ext j
  simp only [baseChangeFreeToResidue, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.restrictScalars_apply, baseChangeBasis_repr_unit,
    freeResidueMap_apply, freeCoefficientMap_apply, freeAtOrigin_apply]
  exact DFunLike.congr_fun he (b.repr x j)

/-- Actual specialization takes a natural homogeneous free part to the generators of that weight. -/
theorem baseChangeFreePiece_map_residue (q : ℕ) :
    (baseChangeFreePiece (R := R) b w q).map (baseChangeFreeToResidue e he b) =
      Finsupp.supported k k {j | w j = q} := by
  rw [baseChangeFreePiece_image]
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rw [baseChangeFreeToResidue_unit]
    exact freeAtOrigin_mem_supported w q hz
  · intro hx
    let z := b.repr.symm (freeConstantLift (σ := σ) x)
    refine ⟨baseChangeUnit (R := R) z, ⟨z, ?_, rfl⟩, ?_⟩
    · change b.repr z ∈ weightedFreePiece w q
      simp only [z, LinearEquiv.apply_symm_apply]
      exact freeConstantLift_mem_weightedFreePiece w q hx
    · rw [baseChangeFreeToResidue_unit]
      simp only [z, LinearEquiv.apply_symm_apply, freeAtOrigin_constantLift]

/-- In basis coordinates this evaluation is the true tensor specialization x -> 1 tensor x. -/
theorem baseChangeFreeToResidue_eq_tmul (x : R ⊗[MvPolynomial σ k] M) :
    letI := e.toAlgebra
    (((b.baseChange R).baseChange k).repr ((1 : k) ⊗ₜ[R] x)) =
      baseChangeFreeToResidue e he b x := by
  letI := e.toAlgebra
  ext j
  rw [Module.Basis.baseChange_repr_tmul]
  change algebraMap R k ((b.baseChange R).repr x j) • (1 : k) = e ((b.baseChange R).repr x j)
  simp only [Algebra.smul_def, mul_one]
  rfl

end BPFixedPoints.ResolutionTools
