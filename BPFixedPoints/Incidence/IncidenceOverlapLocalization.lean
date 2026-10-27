import BPFixedPoints.Incidence.CechOverlapFractions
import BPFixedPoints.Incidence.KoszulFaceRestriction
import BPFixedPoints.Incidence.IncidenceAffineCharts

/-! # Actual incidence quotients on adjacent overlaps are chart localizations

Prove localization directly on the existing quotient rings, using fraction
normal forms and injectivity of their maps into the common torus. No gluing
along the common torus alone is used.
-/

namespace BPFixedPoints.Multigraph
open MvPolynomial CechProduct AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (σ : V → Bool) (v : V) (b : Bool)

/-- The vertex coordinate in the actual quotient chart. -/
noncomputable def incidenceOverlapDen : G.IncFaceRing (chartFace (Function.update σ v b)) :=
  Ideal.Quotient.mk _ (C (overlapDen ℂ σ v b))

@[simp] theorem incFaceRestriction_C (r : FaceRing ℂ (chartFace (Function.update σ v b))) :
    G.incFaceRestriction σ v b (Ideal.Quotient.mk _ (C r)) =
      Ideal.Quotient.mk _ (C (chartRestriction ℂ σ v b r)) := by
  rw [G.incFaceRestriction_mk]
  simp only [chartPolynomialRestriction, mapAlgHom_apply, map_C]
  rfl

@[simp] theorem incFaceRestriction_X (i : IncCoeffIdx E) :
    G.incFaceRestriction σ v b (Ideal.Quotient.mk _ (X i)) = Ideal.Quotient.mk _ (X i) := by
  rw [G.incFaceRestriction_mk]
  simp only [chartPolynomialRestriction, mapAlgHom_apply, map_X]

/-- The actual quotient coordinate is invertible on the adjacent overlap. -/
theorem incidenceOverlapDen_isUnit :
    IsUnit (G.incFaceRestriction σ v b (G.incidenceOverlapDen σ v b)) := by
  rw [incidenceOverlapDen, G.incFaceRestriction_C]
  exact (chartRestriction_overlapDen_isUnit ℂ σ v b).map
    ((Ideal.Quotient.mk (G.incFaceIdeal (overlapFace σ v))).comp C)

/-- Every actual incidence-overlap element has a denominator that is a power
of the source-chart vertex coordinate. -/
theorem incidenceOverlap_fraction (y : G.IncFaceRing (overlapFace σ v)) :
    ∃ (n : ℕ) (x : G.IncFaceRing (chartFace (Function.update σ v b))),
      y * (G.incFaceRestriction σ v b (G.incidenceOverlapDen σ v b))^n =
        G.incFaceRestriction σ v b x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  let χ := G.incFaceRestriction σ v b
  let d := G.incidenceOverlapDen σ v b
  let π := Ideal.Quotient.mk (G.incFaceIdeal (overlapFace σ v))
  induction p using MvPolynomial.induction_on with
  | C r =>
      obtain ⟨n, a, ha⟩ := chartRestriction_fraction ℂ σ v b r
      refine ⟨n, Ideal.Quotient.mk _ (C a), ?_⟩
      have h := congrArg (fun z => π (C z)) ha
      simpa only [map_mul, map_pow, incidenceOverlapDen, G.incFaceRestriction_C] using h
  | add p q hp hq =>
      obtain ⟨n, x, hx⟩ := hp
      obtain ⟨m, z, hz⟩ := hq
      refine ⟨n+m, x*d^m+z*d^n, ?_⟩
      change π (p+q)*(χ d)^(n+m) = χ (x*d^m+z*d^n)
      calc
        _ = (π p*(χ d)^n)*(χ d)^m + (π q*(χ d)^m)*(χ d)^n := by
          rw [map_add, pow_add]; ring
        _ = χ x*(χ d)^m + χ z*(χ d)^n := by rw [hx, hz]
        _ = _ := by rw [map_add, map_mul, map_mul, map_pow, map_pow]
  | mul_X p i hp =>
      obtain ⟨n, x, hx⟩ := hp
      refine ⟨n, x * Ideal.Quotient.mk _ (X i), ?_⟩
      change π (p*X i)*(χ d)^n = χ (x * Ideal.Quotient.mk _ (X i))
      rw [map_mul, map_mul, G.incFaceRestriction_X]
      calc
        _ = (π p*(χ d)^n)*π (X i) := by ring
        _ = _ := by rw [hx]

/-- Coefficient action induced by the actual quotient restriction. -/
noncomputable abbrev incidenceOverlapAlgebra :
    Algebra (G.IncFaceRing (chartFace (Function.update σ v b)))
      (G.IncFaceRing (overlapFace σ v)) :=
  (G.incFaceRestriction σ v b).toRingHom.toAlgebra' (fun c x => by
    exact mul_comm ((G.incFaceRestriction σ v b) c) x)

/-- The actual incidence quotient on an adjacent overlap is localization of
either actual quotient chart, not merely a map into a common ambient field. -/
theorem incidenceOverlap_isLocalization :
    letI := G.incidenceOverlapAlgebra σ v b
    IsLocalization.Away (G.incidenceOverlapDen σ v b) (G.IncFaceRing (overlapFace σ v)) := by
  letI := G.incidenceOverlapAlgebra σ v b
  apply IsLocalization.Away.mk
  · exact G.incidenceOverlapDen_isUnit σ v b
  · exact G.incidenceOverlap_fraction σ v b
  · intro x y h
    refine ⟨0, ?_⟩
    simpa only [pow_zero, one_mul] using G.incFaceRestriction_injective σ v b h

end BPFixedPoints.Multigraph
