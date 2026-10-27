import BPFixedPoints.Incidence.WeightedGradedImage
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Natural image grading on the actual scalar-extended free terms -/

namespace BPFixedPoints.ResolutionTools

open Finsupp MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {k σ R J M : Type*} [Field k] [CommRing R] [Algebra k R]
  [Algebra (MvPolynomial σ k) R] [IsScalarTower k (MvPolynomial σ k) R]
  [AddCommGroup M] [Module (MvPolynomial σ k) M] [Module k M]
  [IsScalarTower k (MvPolynomial σ k) M]
  (b : Module.Basis J (MvPolynomial σ k) M) (w : J → ℕ)

/-- The actual scalar-extension map, restricted to the ground field. -/
noncomputable def baseChangeUnit : M →ₗ[k] R ⊗[MvPolynomial σ k] M :=
  (TensorProduct.mk (MvPolynomial σ k) R M 1).restrictScalars k

@[simp] theorem baseChangeUnit_apply (x : M) :
    baseChangeUnit (R := R) x = (1 : R) ⊗ₜ[MvPolynomial σ k] x := rfl

theorem baseChangeBasis_repr_unit (x : M) :
    (b.baseChange R).repr (baseChangeUnit (R := R) x) =
      freeCoefficientMap (IsScalarTower.toAlgHom k (MvPolynomial σ k) R) (b.repr x) := by
  ext j
  rw [baseChangeUnit_apply, Module.Basis.baseChange_repr_tmul, freeCoefficientMap_apply]
  simp only [Algebra.smul_def, mul_one]
  rfl

/-- Use the image coefficient grading and the original generator shifts. -/
noncomputable def baseChangeFreePiece (q : ℤ) : Submodule k (R ⊗[MvPolynomial σ k] M) :=
  (shiftedFreePiece
    (gradedImagePiece (homogeneousSubmodule σ k) (IsScalarTower.toAlgHom k (MvPolynomial σ k) R)) w q).comap
      ((b.baseChange R).repr.restrictScalars k).toLinearMap

/-- The natural shifted grading after a coefficient quotient is the image grading of the old term. -/
theorem baseChangeFreePiece_image (q : ℤ) :
    baseChangeFreePiece (R := R) b w q =
      ((weightedFreePiece w q).comap (b.repr.restrictScalars k).toLinearMap).map
        (baseChangeUnit (R := R)) := by
  ext x
  constructor
  · intro hx
    change (b.baseChange R).repr x ∈ shiftedFreePiece _ w q at hx
    rw [shiftedFreePiece_image] at hx
    obtain ⟨y, hy, he⟩ := hx
    refine ⟨b.repr.symm y, ?_, ?_⟩
    · change b.repr (b.repr.symm y) ∈ weightedFreePiece w q
      simpa using hy
    · apply (b.baseChange R).repr.injective
      rw [baseChangeBasis_repr_unit, LinearEquiv.apply_symm_apply, he]
  · rintro ⟨y, hy, rfl⟩
    change (b.baseChange R).repr (baseChangeUnit (R := R) y) ∈ shiftedFreePiece _ w q
    rw [baseChangeBasis_repr_unit, shiftedFreePiece_image]
    exact ⟨b.repr y, hy, rfl⟩

section Maps

variable {N : Type*} [AddCommGroup N] [Module (MvPolynomial σ k) N] [Module k N]
  [IsScalarTower k (MvPolynomial σ k) N]

/-- Ground-field restriction, with the scalar towers resolved before concrete specialization. -/
noncomputable def baseChangeGroundLinear (f : M →ₗ[MvPolynomial σ k] N) :
    (R ⊗[MvPolynomial σ k] M) →ₗ[k] (R ⊗[MvPolynomial σ k] N) :=
  (f.baseChange R).restrictScalars k

@[simp] theorem baseChangeUnit_naturality (f : M →ₗ[MvPolynomial σ k] N) (x : M) :
    f.baseChange R (baseChangeUnit (R := R) x) = baseChangeUnit (R := R) (f x) := rfl

/-- A homogeneous map remains homogeneous for the actual image components. -/
theorem baseChange_image_homogeneous (f : M →ₗ[MvPolynomial σ k] N)
    (P : Submodule k M) (Q : Submodule k N) (hf : ∀ x ∈ P, f x ∈ Q)
    {x : R ⊗[MvPolynomial σ k] M} (hx : x ∈ P.map (baseChangeUnit (R := R))) :
    f.baseChange R x ∈ Q.map (baseChangeUnit (R := R)) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨f y, hf y hy, rfl⟩

end Maps

variable [GradedAlgebra (gradedImagePiece (homogeneousSubmodule σ k)
  (IsScalarTower.toAlgHom k (MvPolynomial σ k) R))]

theorem iSup_baseChangeFreePiece : (⨆ q : ℕ, baseChangeFreePiece (R := R) b w q) = ⊤ := by
  unfold baseChangeFreePiece
  simp_rw [Submodule.comap_equiv_eq_map_symm]
  rw [← Submodule.map_iSup, iSup_shiftedFreePiece, Submodule.map_top,
    LinearMap.range_eq_top.mpr ((b.baseChange R).repr.restrictScalars k).symm.surjective]

theorem iSupIndep_baseChangeFreePiece :
    iSupIndep (fun q : ℕ => baseChangeFreePiece (R := R) b w q) := by
  apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr
  intro s x hx hs q hq
  apply (b.baseChange R).repr.injective
  rw [map_zero]
  apply shiftedFreePiece_sum_unique _ w s (fun n => (b.baseChange R).repr (x n)) hx _ q hq
  simpa only [map_sum, map_zero] using congrArg (b.baseChange R).repr hs

end BPFixedPoints.ResolutionTools
