import BPFixedPoints.Incidence.KoszulCech
import BPFixedPoints.Incidence.ResolutionMinimality

/-! # Minimality of the constructed finite free model -/

namespace BPFixedPoints.Multigraph

open Finsupp IncidencePerturbation ResolutionTools

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Maximal ideal of the coefficient origin. -/
noncomputable def incCoeffAugmentationIdeal (E : Type) : Ideal (IncCoeffRing E) :=
  RingHom.ker (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)

theorem incEdgeAction_mem_augmentation (e : E)
    (x : IncCechModule (V := V) (E := E)) :
    G.incEdgeAction e x ∈ incCoeffAugmentationIdeal E •
      (⊤ : Submodule (IncCoeffRing E) (IncCechModule (V := V) (E := E))) := by
  simp only [incEdgeAction, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro α _
  apply Submodule.sum_mem
  intro β _
  apply Submodule.smul_mem_smul
  · change MvPolynomial.constantCoeff (MvPolynomial.X (e, α, β) : IncCoeffRing E) = 0
    exact MvPolynomial.constantCoeff_X (R := ℂ) (e, α, β)
  · exact Submodule.mem_top

theorem incKoszulPerturbation_mem_augmentation
    (x : IncTotalModule (V := V) (E := E)) :
    G.incKoszulPerturbation x ∈ incCoeffAugmentationIdeal E •
      (⊤ : Submodule (IncCoeffRing E) (IncTotalModule (V := V) (E := E))) := by
  classical
  rw [← x.sum_single, map_finsuppSum]
  apply Submodule.sum_mem
  intro S hS
  change G.incKoszulPerturbation (single S (x S)) ∈ _
  rw [G.incKoszulPerturbation_single]
  apply Submodule.sum_mem
  intro e he
  apply map_mem_ideal_smul_top (incCoeffAugmentationIdeal E) (Finsupp.lsingle (S.erase e))
  apply map_mem_ideal_smul_top (incCoeffAugmentationIdeal E)
    (CechProduct.contraction (IncCoeffRing E) (G.deg (S.erase e))).sign
  exact Submodule.smul_mem _ _ (G.incEdgeAction_mem_augmentation e (x S))

/-- Every differential coefficient vanishes at the coefficient origin. -/
theorem incResolutionDifferential_minimal (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    G.incResolutionDifferential x ∈ incCoeffAugmentationIdeal E •
      (⊤ : Submodule (IncCoeffRing E) (G.IncResolutionBasis →₀ IncCoeffRing E)) :=
  G.incCechContraction.transfer_mem_ideal_smul_top (incCoeffAugmentationIdeal E)
    G.incKoszulPerturbation G.incKoszulPerturbation_mem_augmentation x

end BPFixedPoints.Multigraph
