import BPFixedPoints.Incidence.ResolutionGrading
import BPFixedPoints.Incidence.Perturbation

/-!
# Minimality of a perturbed differential

If Koszul coefficients lie in the coefficient ideal, so do coefficients of
the differential after linear contraction, projection and the finite inverse.
-/

namespace BPFixedPoints.IncidencePerturbation

open ResolutionTools

universe u

variable {R M H : Type u} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]

theorem correction_mem_ideal_smul_top
    (I : Ideal R) (δ h : Module.End R M)
    (hδ : ∀ x, δ x ∈ I • (⊤ : Submodule R M)) (x : M) :
    correction δ h x ∈ I • (⊤ : Submodule R M) := by
  change (Ring.inverse (1 + δ * h)) (δ x) ∈ I • (⊤ : Submodule R M)
  exact map_mem_ideal_smul_top I (Ring.inverse (1 + δ * h)) (hδ x)

/-- The transferred differential of an ideal-valued perturbation remains ideal-valued. -/
theorem Contraction.transfer_mem_ideal_smul_top
    (C : Contraction R M H) (I : Ideal R) (δ : Module.End R M)
    (hδ : ∀ x, δ x ∈ I • (⊤ : Submodule R M)) (x : H) :
    C.transfer δ x ∈ I • (⊤ : Submodule R H) := by
  change C.p (correction δ C.h (C.i x)) ∈ I • (⊤ : Submodule R H)
  exact map_mem_ideal_smul_top I C.p
    (correction_mem_ideal_smul_top I δ C.h hδ (C.i x))

end BPFixedPoints.IncidencePerturbation
