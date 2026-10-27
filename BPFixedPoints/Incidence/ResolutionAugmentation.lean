import BPFixedPoints.Incidence.ResolutionAugmentationBridge
import BPFixedPoints.Incidence.ResolutionZeroExactness
import BPFixedPoints.Incidence.QuotientCechSections

/-!
# Augmentation to the actual incidence ring

Combine two finite contractions with gluing of the local-quotient Čech degree-zero
kernel. The resulting coefficient-linear map is surjective and its kernel
is exactly the first boundaries in the finite free model.
-/

namespace BPFixedPoints.Multigraph

open CechProduct ResolutionTools

set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance : Algebra (IncCoeffRing E) G.IncTorusRing :=
  G.incTorusCoeffHom.toRingHom.toAlgebra

noncomputable local instance : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra

theorem incResolutionTorusAugmentation_mem
    (x : G.IncResolutionBasis →₀ IncCoeffRing E)
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) :
    G.incResolutionTorusAugmentation x ∈ G.IncidenceRing := by
  rw [G.incResolutionTorusAugmentation_apply]
  exact G.incQuotientCycle_torus_mem _ (G.incResolutionQuotient_mem_zero x hx)
    (G.incResolutionQuotient_cycle x hx)

/-- Augmentation of the free resolution to the incidence ring with its original coefficient action. -/
noncomputable def incResolutionAugmentation :
    gradedPiece (IncCoeffRing E) G.incResolutionDegree 0 →ₗ[IncCoeffRing E] G.IncidenceRing where
  toFun x := ⟨G.incResolutionTorusAugmentation x.val,
    G.incResolutionTorusAugmentation_mem x.val x.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact G.incResolutionTorusAugmentation.map_add x.val y.val
  map_smul' r x := by
    apply Subtype.ext
    exact G.incResolutionTorusAugmentation.map_smul r x.val

@[simp] theorem incResolutionAugmentation_val
    (x : gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) :
    (G.incResolutionAugmentation x).val = G.incResolutionTorusAugmentation x.val := rfl

/-- The augmentation kernel equals exactly the boundaries from degree one. -/
theorem incResolutionAugmentation_exact
    (x : gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) :
    G.incResolutionAugmentation x = 0 ↔
      ∃ y, y ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 1 ∧
        G.incResolutionDifferential y = x.val := by
  have hz : G.incResolutionAugmentation x = 0 ↔
      G.incKoszulContraction.p (G.incResolutionInclusion x.val) = 0 := by
    constructor
    · intro h
      apply G.incQuotientCycle_eq_zero_of_torus_eq_zero _
        (G.incResolutionQuotient_mem_zero x.val x.property)
        (G.incResolutionQuotient_cycle x.val x.property)
      rw [← G.incResolutionTorusAugmentation_apply]
      exact congrArg Subtype.val h
    · intro h
      apply Subtype.ext
      change G.incResolutionTorusAugmentation x.val = 0
      rw [G.incResolutionTorusAugmentation_apply, h]
      exact map_zero _
  exact hz.trans (G.incResolutionDifferential_exact_zero_of_projection_zero x.val x.property)

/-- Every incidence section is the image of a degree-zero free-model element. -/
theorem incResolutionAugmentation_surjective : Function.Surjective G.incResolutionAugmentation := by
  intro u
  obtain ⟨q, hq, hdq, hqu⟩ := G.exists_incQuotientCycle_of_incidence u
  obtain ⟨x, hx, hxq⟩ := G.exists_incResolution_lift_quotientCycle q hq hdq
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  change G.incResolutionTorusAugmentation x = u.val
  rw [G.incResolutionTorusAugmentation_apply, hxq]
  exact hqu

end BPFixedPoints.Multigraph
