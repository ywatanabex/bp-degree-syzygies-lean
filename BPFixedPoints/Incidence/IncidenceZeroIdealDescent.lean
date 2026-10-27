import BPFixedPoints.Incidence.IncidenceEquationTransitions
import BPFixedPoints.Incidence.IncidenceFaceRefinement

/-! # Descent of the original homogeneous zero ideals on all face overlaps

Refinement sends each edge equation to an explicit unit times the same edge
equation. Consequently extension of the source zero ideal is exactly the target
zero ideal. This is an equality before taking incidence quotients.
-/

namespace BPFixedPoints.Multigraph
open MvPolynomial CechProduct
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Extension of the actual homogeneous incidence ideal is the actual overlap ideal. -/
theorem incFaceIdeal_map_refinement {q r : V → Fin 3} (h : FaceRefines q r) :
    (G.incFaceIdeal q).map (facePolynomialRefinement ℂ (IncCoeffIdx E) h).toRingHom =
      G.incFaceIdeal r := by
  apply le_antisymm
  · rw [incFaceIdeal, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨p, ⟨e, rfl⟩, rfl⟩
    change facePolynomialRefinement ℂ (IncCoeffIdx E) h (G.incFaceEquation q e) ∈ G.incFaceIdeal r
    rw [G.incFaceEquation_refinement]
    exact (G.incFaceIdeal r).mul_mem_left _ (Ideal.subset_span ⟨e, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨e, rfl⟩
    change G.incFaceEquation r e ∈ (G.incFaceIdeal q).map (facePolynomialRefinement ℂ (IncCoeffIdx E) h).toRingHom
    let u := G.incidenceEquationTransitionUnit h e
    have hm : (u : MvPolynomial (IncCoeffIdx E) (FaceRing ℂ r)) * G.incFaceEquation r e ∈
        (G.incFaceIdeal q).map (facePolynomialRefinement ℂ (IncCoeffIdx E) h).toRingHom := by
      rw [← G.incFaceEquation_refinement]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨e, rfl⟩)
    have hi := ((G.incFaceIdeal q).map (facePolynomialRefinement ℂ (IncCoeffIdx E) h).toRingHom).mul_mem_left
      (↑u⁻¹) hm
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using hi

/-- Pulling back the overlap zero ideal to a parent ambient face gives exactly
the original parent zero ideal; no additional equations appear after localization. -/
theorem incFaceIdeal_comap_refinement {q r : V → Fin 3} (h : FaceRefines q r) :
    (G.incFaceIdeal r).comap (facePolynomialRefinement ℂ (IncCoeffIdx E) h).toRingHom =
      G.incFaceIdeal q := by
  ext p
  rw [Ideal.mem_comap]
  change facePolynomialRefinement ℂ (IncCoeffIdx E) h p ∈ G.incFaceIdeal r ↔ p ∈ G.incFaceIdeal q
  rw [← Ideal.Quotient.eq_zero_iff_mem,
    ← G.incFaceRefinement_mk, ← map_zero (G.incFaceRefinement h),
    (G.incFaceRefinement_injective h).eq_iff, Ideal.Quotient.eq_zero_iff_mem]

end BPFixedPoints.Multigraph
