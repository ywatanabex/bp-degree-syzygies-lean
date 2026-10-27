import BPFixedPoints.Incidence.KoszulFaceCoefficient
import BPFixedPoints.Incidence.ResolutionExactness

/-!
# Coefficient-linear map from the finite free model to the common torus

Include a degree-zero element in the total complex and evaluate its empty
exterior component on the all-left chart. Two chain maps prove that projection
to local quotients is a Čech degree-zero cycle.
-/

namespace BPFixedPoints.Multigraph

open CechProduct ResolutionTools

set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance : Algebra (IncCoeffRing E) G.IncTorusRing :=
  G.incTorusCoeffHom.toRingHom.toAlgebra

/-- Coefficient-linear evaluation from the free state-cohomology module to the common torus. -/
noncomputable def incResolutionTorusAugmentation :
    (G.IncResolutionBasis →₀ IncCoeffRing E) →ₗ[IncCoeffRing E] G.IncTorusRing :=
  (G.incFaceRawEval (chartFace (fun _ : V => false))).comp G.incResolutionInclusion

theorem incResolutionTorusAugmentation_apply
    (x : G.IncResolutionBasis →₀ IncCoeffRing E) :
    G.incResolutionTorusAugmentation x =
      G.incFaceToTorus (chartFace (fun _ : V => false))
        (G.incKoszulContraction.p (G.incResolutionInclusion x)
          (chartFace (fun _ : V => false))) :=
  G.incFaceRawEval_eq_projection _ _

theorem incResolutionQuotient_mem_zero
    (x : G.IncResolutionBasis →₀ IncCoeffRing E)
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) :
    G.incKoszulContraction.p (G.incResolutionInclusion x) ∈ G.incQuotientPiece 0 := by
  have hi := G.incResolutionInclusion_degree 0 x hx
  have hp := G.incKoszulContraction_p_shifts 0 (G.incResolutionInclusion x) hi
  simpa only [zero_add] using hp

theorem incResolutionQuotient_cycle
    (x : G.IncResolutionBasis →₀ IncCoeffRing E)
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) :
    G.incQuotientDifferential (G.incKoszulContraction.p (G.incResolutionInclusion x)) = 0 := by
  have hi : G.incTotalDifferential (G.incResolutionInclusion x) = 0 := by
    calc
      _ = G.incResolutionInclusion (G.incResolutionDifferential x) :=
        LinearMap.congr_fun G.incResolutionInclusion_chain x
      _ = 0 := by rw [G.incResolutionDifferential_zero_degree x hx, map_zero]
  have hp := LinearMap.congr_fun G.incQuotientProjection_chain (G.incResolutionInclusion x)
  change G.incQuotientProjection (G.incTotalDifferential (G.incResolutionInclusion x)) =
    G.incQuotientDifferential (G.incQuotientProjection (G.incResolutionInclusion x)) at hp
  rw [hi, map_zero, G.incQuotientProjection_eq] at hp
  exact hp.symm

end BPFixedPoints.Multigraph
