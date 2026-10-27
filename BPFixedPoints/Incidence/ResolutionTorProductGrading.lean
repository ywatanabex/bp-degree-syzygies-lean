import BPFixedPoints.Incidence.ResolutionCupInternalGrading
import BPFixedPoints.Incidence.ResolutionTorAlgebra
import BPFixedPoints.Incidence.NaturalGradedResolution

/-!
# Standard Tor multiplication and the natural internal grading

For Tor pieces obtained from the original ring's natural grading, prove
additivity of internal degree using the resolution product and comparison
with the actual derived functor.
-/

namespace BPFixedPoints.Multigraph

open ResolutionTools
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance torProductGradingOriginAlgebra : Algebra (IncCoeffRing E) ℂ :=
  (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra

noncomputable local instance torProductGradingRingAlgebra : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra

/-- Boundaries in the actual resolution vanish under origin specialization. -/
theorem incFreeTermToTor_boundary (p : ℕ) (x : G.IncFreeTerm (p + 1)) :
    G.incFreeTermToTor p (G.incFreeTermDifferential p x) = 0 := by
  apply G.incidenceTorToFull_injective p
  rw [G.incidenceTorToFull_class, map_zero]
  change (1 : ℂ) ⊗ₜ[IncCoeffRing E] G.incResolutionDifferential x.val = 0
  exact tmul_eq_zero_of_mem_augmentation (G.incResolutionDifferential_minimal x.val) 1

/-- Degree-zero elements with the same augmentation give the same Tor class. -/
theorem incFreeTermToTor_eq_of_augmentation_eq (x y : G.IncFreeTerm 0)
    (h : G.incResolutionAugmentation x = G.incResolutionAugmentation y) :
    G.incFreeTermToTor 0 x = G.incFreeTermToTor 0 y := by
  have hz : x - y ∈ LinearMap.range (G.incFreeTermDifferential 0) := by
    rw [G.incFreeTermDifferential_augmentation_exact, LinearMap.mem_ker]
    exact (G.incResolutionAugmentation.map_sub x y).trans (sub_eq_zero.mpr h)
  obtain ⟨z, hz⟩ := hz
  apply sub_eq_zero.mp
  rw [← map_sub, ← hz]
  exact G.incFreeTermToTor_boundary 0 z

/-- The unit is represented by a homogeneous lift of the original ring's degree-zero element 1. -/
theorem incidenceTorOne_internal_degree :
    G.incidenceTorOne ∈ G.incidenceTorInternalPiece 0 0 := by
  obtain ⟨x, hx, hε⟩ := G.incResolutionAugmentation_graded_surjective 0 1
    G.one_mem_incidenceCoefficientPiece
  refine ⟨x, hx, ?_⟩
  apply G.incFreeTermToTor_eq_of_augmentation_eq
  exact hε.trans (Classical.choose_spec (G.incResolutionAugmentation_surjective 1)).symm

/-- Both homological degree and internal degree from the natural ring grading are additive. -/
theorem incidenceTorProduct_internal_degree (p q a b : ℕ)
    {x : G.incidenceTor p} {y : G.incidenceTor q}
    (hx : x ∈ G.incidenceTorInternalPiece p a)
    (hy : y ∈ G.incidenceTorInternalPiece q b) :
    G.incidenceTorProduct p q x y ∈ G.incidenceTorInternalPiece (p + q) (a + b) := by
  rcases hx with ⟨u, hu, rfl⟩
  rcases hy with ⟨v, hv, rfl⟩
  rw [G.incidenceTorProduct_eq_transferred]
  refine ⟨⟨G.incResolutionCup u.val v.val,
    G.incResolutionCup_degree p q u.property v.property⟩, ?_, rfl⟩
  apply (G.mem_incFreeTermInternalPiece_iff _ _ _).mpr
  simpa only [Nat.cast_add] using G.incResolutionCup_internal_degree (a : ℤ) (b : ℤ)
    ((G.mem_incFreeTermInternalPiece_iff p a u).mp hu)
    ((G.mem_incFreeTermInternalPiece_iff q b v).mp hv)

end BPFixedPoints.Multigraph
