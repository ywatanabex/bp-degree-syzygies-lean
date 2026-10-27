import BPFixedPoints.Incidence.IncidenceOverlapLocalization
import BPFixedPoints.Incidence.KoszulFaceChart

/-! # Actual open immersions from adjacent incidence overlaps

Every face quotient gives an integral affine scheme. An overlap of two adjacent
charts is the spectrum of its existing incidence quotient, and maps openly into
both original charts. Higher intersections and their gluing are separate steps.
-/

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory CechProduct
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- All actual face rings embed in the original common torus and are domains. -/
instance incFaceRing_isDomain (q : V → Fin 3) : IsDomain (G.IncFaceRing q) :=
  (G.incFaceToTorus_injective q).isDomain (G.incFaceToTorus q).toRingHom

/-- Spectrum of an actual incidence face quotient. -/
noncomputable def incidenceAffineFace (q : V → Fin 3) : Scheme :=
  Spec (CommRingCat.of (G.IncFaceRing q))

instance incidenceAffineFace_isIntegral (q : V → Fin 3) : IsIntegral (G.incidenceAffineFace q) := by
  unfold incidenceAffineFace
  infer_instance

variable (σ : V → Bool) (v : V) (b : Bool)

/-- The scheme map induced by the actual adjacent quotient restriction. -/
noncomputable def incidenceAdjacentFaceMap :
    G.incidenceAffineFace (overlapFace σ v) ⟶
      G.incidenceAffineFace (chartFace (Function.update σ v b)) :=
  Spec.map (CommRingCat.ofHom (G.incFaceRestriction σ v b).toRingHom)

/-- The actual adjacent overlap maps openly into either quotient chart. -/
instance incidenceAdjacentFaceMap_isOpenImmersion :
    IsOpenImmersion (G.incidenceAdjacentFaceMap σ v b) := by
  letI := G.incidenceOverlapAlgebra σ v b
  haveI := G.incidenceOverlap_isLocalization σ v b
  exact IsOpenImmersion.of_isLocalization (G.incidenceOverlapDen σ v b)

/-- Return from the quotient face presentation to the existing original chart scheme. -/
noncomputable def incidenceAdjacentOverlapToChart :
    G.incidenceAffineFace (overlapFace σ v) ⟶
      G.incidenceAffineChart (Function.update σ v b) :=
  G.incidenceAdjacentFaceMap σ v b ≫
    Spec.map (G.incFaceChartEquiv (Function.update σ v b)).symm.toRingEquiv.toCommRingCatIso.hom

/-- The adjacent overlap is an actual open subscheme of either original chart. -/
instance incidenceAdjacentOverlapToChart_isOpenImmersion :
    IsOpenImmersion (G.incidenceAdjacentOverlapToChart σ v b) := by
  unfold incidenceAdjacentOverlapToChart
  infer_instance

end BPFixedPoints.Multigraph
