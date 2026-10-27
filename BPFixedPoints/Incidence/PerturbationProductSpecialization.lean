import BPFixedPoints.Incidence.ResolutionMinimality
import BPFixedPoints.Incidence.DerivedSpecialization
import BPFixedPoints.Incidence.ResolutionExactness
import BPFixedPoints.Incidence.ResolutionFiniteModel

/-!
# Origin specialization of transferred bilinear products

If perturbation has image in the coefficient-origin ideal times the module,
corrections to inclusion and projection vanish at the origin. Thus any
coefficient-bilinear map transferred from the total complex specializes to
the expression using uncorrected inclusion/projection. This lemma does not
itself construct a total-complex product.
-/

namespace BPFixedPoints.IncidencePerturbation

open ResolutionTools
open scoped TensorProduct

universe u
variable {R k M H : Type u} [CommRing R] [CommRing k]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]

namespace Contraction

variable (C : Contraction R M H) (I : Ideal R) (δ : Module.End R M)
  (hδ : ∀ x, δ x ∈ I • (⊤ : Submodule R M))

include hδ in
theorem inclusion_sub_mem_ideal (x : H) :
    C.inclusion δ x - C.i x ∈ I • (⊤ : Submodule R M) := by
  change C.i x - C.h (correction δ C.h (C.i x)) - C.i x ∈ _
  rw [sub_sub_cancel_left]
  exact Submodule.neg_mem _ (map_mem_ideal_smul_top I C.h
    (correction_mem_ideal_smul_top I δ C.h hδ (C.i x)))

include hδ in
theorem projection_sub_mem_ideal (x : M) :
    C.projection δ x - C.p x ∈ I • (⊤ : Submodule R H) := by
  change C.p (x - correction δ C.h (C.h x)) - C.p x ∈ _
  rw [map_sub, sub_sub_cancel_left]
  exact Submodule.neg_mem _ (map_mem_ideal_smul_top I C.p
    (correction_mem_ideal_smul_top I δ C.h hδ (C.h x)))

/-- Transfer a bilinear map using the actual corrected inclusion and projection. -/
noncomputable def transferredPairing (μ : M →ₗ[R] M →ₗ[R] M) : H →ₗ[R] H →ₗ[R] H :=
  (μ.compl₁₂ (C.inclusion δ) (C.inclusion δ)).compr₂ (C.projection δ)

include hδ in
/-- The corrected and uncorrected transfers differ by an element of the coefficient-ideal multiple. -/
theorem transferredPairing_sub_mem_ideal (μ : M →ₗ[R] M →ₗ[R] M) (x y : H) :
    C.transferredPairing δ μ x y - C.p (μ (C.i x) (C.i y)) ∈
      I • (⊤ : Submodule R H) := by
  have hx := C.inclusion_sub_mem_ideal I δ hδ x
  have hy := C.inclusion_sub_mem_ideal I δ hδ y
  have hleft : μ (C.inclusion δ x) (C.inclusion δ y) - μ (C.i x) (C.inclusion δ y) ∈
      I • (⊤ : Submodule R M) := by
    simpa only [map_sub, LinearMap.flip_apply] using map_mem_ideal_smul_top I (μ.flip (C.inclusion δ y)) hx
  have hright : μ (C.i x) (C.inclusion δ y) - μ (C.i x) (C.i y) ∈
      I • (⊤ : Submodule R M) := by
    simpa only [map_sub] using map_mem_ideal_smul_top I (μ (C.i x)) hy
  have hmul : μ (C.inclusion δ x) (C.inclusion δ y) - μ (C.i x) (C.i y) ∈
      I • (⊤ : Submodule R M) := by
    simpa only [sub_add_sub_cancel] using Submodule.add_mem _ hleft hright
  have hp := C.projection_sub_mem_ideal I δ hδ (μ (C.inclusion δ x) (C.inclusion δ y))
  have hm := map_mem_ideal_smul_top I C.p hmul
  change C.projection δ (μ (C.inclusion δ x) (C.inclusion δ y)) -
    C.p (μ (C.i x) (C.i y)) ∈ _
  simpa only [map_sub, sub_add_sub_cancel] using Submodule.add_mem _ hp hm

/-- Comparison of transferred products under actual tensor specialization at the coefficient origin. -/
theorem transferredPairing_tmul (f : R →+* k)
    (hδf : ∀ x, δ x ∈ RingHom.ker f • (⊤ : Submodule R M))
    (μ : M →ₗ[R] M →ₗ[R] M) (x y : H) :
    letI : Algebra R k := f.toAlgebra
    (1 : k) ⊗ₜ[R] C.transferredPairing δ μ x y =
      (1 : k) ⊗ₜ[R] C.p (μ (C.i x) (C.i y)) := by
  letI : Algebra R k := f.toAlgebra
  have h := tmul_eq_zero_of_mem_augmentation
    (C.transferredPairing_sub_mem_ideal (RingHom.ker f) δ hδf μ x y) (1 : k)
  simpa only [TensorProduct.tmul_sub, sub_eq_zero] using h

end Contraction
end BPFixedPoints.IncidencePerturbation

namespace BPFixedPoints.Multigraph

open IncidencePerturbation
open scoped TensorProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Compute transferred bilinear maps at the origin for the actual finite incidence perturbation. No chain-product axioms are assumed for μ, so this is not itself the identification with standard Tor multiplication. -/
theorem incTransferredPairing_atOrigin
    (μ : IncTotalModule (V := V) (E := E) →ₗ[IncCoeffRing E]
      IncTotalModule (V := V) (E := E) →ₗ[IncCoeffRing E] IncTotalModule (V := V) (E := E))
    (x y : G.IncResolutionBasis →₀ IncCoeffRing E) :
    letI : Algebra (IncCoeffRing E) ℂ :=
      (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra
    (1 : ℂ) ⊗ₜ[IncCoeffRing E]
        G.incResolutionProjection (μ (G.incResolutionInclusion x) (G.incResolutionInclusion y)) =
      (1 : ℂ) ⊗ₜ[IncCoeffRing E] G.incCechContraction.p
        (μ (G.incCechContraction.i x) (G.incCechContraction.i y)) :=
  G.incCechContraction.transferredPairing_tmul G.incKoszulPerturbation
    MvPolynomial.constantCoeff G.incKoszulPerturbation_mem_augmentation μ x y

end BPFixedPoints.Multigraph
