import BPFixedPoints.Incidence.ResolutionCupAugmentation
import BPFixedPoints.Incidence.GradedFreePairing
import BPFixedPoints.Incidence.MinimalLiftComparison
import BPFixedPoints.Incidence.ResolutionTor

/-!
# Multiplication lifts of the original ring and their standard comparison

A multiplication lift preserves degrees, satisfies Leibniz and is multiplicative
for the original augmentation. Compare two choices by homotopy on the actual
tensor complex of projective terms.
-/

set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

namespace BPFixedPoints.Multigraph

open Finsupp ResolutionTools CategoryTheory
open scoped TensorProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance : Algebra (IncCoeffRing E) G.IncTorusRing :=
  G.incTorusCoeffHom.toRingHom.toAlgebra

/-- Actual bilinear chain map on the free resolution lifting multiplication in the original incidence ring. -/
structure IncResolutionMultiplication extends
    GradedFreePairing G.incResolutionDegree G.incResolutionDifferential where
  augmentation : ∀ (x y : G.IncResolutionBasis →₀ IncCoeffRing E),
    x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0 →
    y ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0 →
    G.incResolutionTorusAugmentation (mul x y) =
      G.incResolutionTorusAugmentation x * G.incResolutionTorusAugmentation y

/-- Multiplication lift obtained from the exterior Alexander–Whitney product. -/
noncomputable def incResolutionMultiplication : G.IncResolutionMultiplication where
  mul := G.incResolutionCup
  homogeneous := G.incResolutionCup_degree
  augmentation := G.incResolutionTorusAugmentation_cup
  leibniz x y := by
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']; abel
    | single a r =>
      rw [G.incResolutionCup_leibniz (G.incResolutionDegree a) (single_mem_supported _ _ rfl),
        gradedParity_single, LinearMap.map_smul₂]

noncomputable abbrev incTensorResolutionComplex :=
  gradedTensorComplex G.incResolutionDegree G.incResolutionDifferential
    G.incResolutionDifferential_hasDegree G.incResolutionDifferential_sq

namespace IncResolutionMultiplication

variable {G} (μ : G.IncResolutionMultiplication)

noncomputable def chainMap : G.incTensorResolutionComplex ⟶ G.incFreeResolution.complex :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (μ.toGradedFreePairing.component n)) (fun n => by
    rw [G.incFreeResolution_d, gradedTensorComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact μ.toGradedFreePairing.linearize_chain x.val)

theorem augmentation_linearize_eq (ν : G.IncResolutionMultiplication)
    (x : gradedPiece (IncCoeffRing E)
      (fun a : G.IncResolutionBasis × G.IncResolutionBasis =>
        G.incResolutionDegree a.1 + G.incResolutionDegree a.2) 0) :
    G.incResolutionTorusAugmentation (μ.toGradedFreePairing.linearize x.val) =
      G.incResolutionTorusAugmentation (ν.toGradedFreePairing.linearize x.val) := by
  rw [← x.val.sum_single]
  simp only [map_finsuppSum, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨a, b⟩ hab
  rw [GradedFreePairing.linearize_single, GradedFreePairing.linearize_single]
  have hd : G.incResolutionDegree a + G.incResolutionDegree b = 0 :=
    (mem_supported (IncCoeffRing E) x.val).mp x.property hab
  have ha : G.incResolutionDegree a = 0 := by omega
  have hb : G.incResolutionDegree b = 0 := by omega
  rw [μ.augmentation _ _ (single_mem_supported _ _ ha) (single_mem_supported _ _ hb),
    ν.augmentation _ _ (single_mem_supported _ _ ha) (single_mem_supported _ _ hb)]

theorem chainMap_augmentation_eq (ν : G.IncResolutionMultiplication) :
    μ.chainMap ≫ G.incFreeResolution.π = ν.chainMap ≫ G.incFreeResolution.π := by
  apply HomologicalComplex.to_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change G.incResolutionTorusAugmentation (μ.toGradedFreePairing.linearize x.val) =
    G.incResolutionTorusAugmentation (ν.toGradedFreePairing.linearize x.val)
  exact μ.augmentation_linearize_eq ν x

/-- Two multiplication lifts give the same chain map after coefficient-origin specialization. -/
theorem specialized_chainMap_eq (ν : G.IncResolutionMultiplication) (n : ℕ) :
    (ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)).map
        (μ.chainMap.f n) =
      (ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)).map
        (ν.chainMap.f n) := by
  apply specialized_lifts_eq _ G.incFreeResolution μ.chainMap ν.chainMap
    (μ.chainMap_augmentation_eq ν)
  · exact gradedTensorComplex_minimal G.incResolutionDegree G.incResolutionDifferential
      G.incResolutionDifferential_hasDegree G.incResolutionDifferential_sq
      (incCoeffAugmentationIdeal E) G.incResolutionDifferential_minimal
  · exact G.incFreeResolution_minimal

end IncResolutionMultiplication
end BPFixedPoints.Multigraph
