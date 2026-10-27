import BPFixedPoints.Incidence.CechRefinementLocalization
import BPFixedPoints.Incidence.IncidenceFaceRefinement
import BPFixedPoints.Incidence.IncidenceAdjacentOverlaps

/-! # Actual incidence quotients on higher overlaps are face localizations

Prove localization directly on the existing quotient rings, using fraction
normal forms and injectivity of their maps into the common torus. This is proved on the original incidence quotient rings.
-/

namespace BPFixedPoints.Multigraph
open MvPolynomial CechProduct AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) {q r : V → Fin 3} (h : FaceRefines q r)

/-- The product of newly inverted vertex coordinates in the original quotient face. -/
noncomputable def incidenceRefinementDen (_h : FaceRefines q r) : G.IncFaceRing q :=
  Ideal.Quotient.mk _ (C (refinementDen ℂ q r))

@[simp] theorem incFaceRefinement_C (c : FaceRing ℂ q) :
    G.incFaceRefinement h (Ideal.Quotient.mk _ (C c)) =
      Ideal.Quotient.mk _ (C (faceRefinementMap ℂ h c)) := by
  rw [G.incFaceRefinement_mk]
  simp only [facePolynomialRefinement, mapAlgHom_apply, map_C]
  rfl

@[simp] theorem incFaceRefinement_X (i : IncCoeffIdx E) :
    G.incFaceRefinement h (Ideal.Quotient.mk _ (X i)) = Ideal.Quotient.mk _ (X i) := by
  rw [G.incFaceRefinement_mk]
  simp only [facePolynomialRefinement, mapAlgHom_apply, map_X]

/-- The product becomes invertible on the original higher-overlap quotient. -/
theorem incidenceRefinementDen_isUnit :
    IsUnit (G.incFaceRefinement h (G.incidenceRefinementDen h)) := by
  rw [incidenceRefinementDen, G.incFaceRefinement_C]
  exact (faceRefinement_den_isUnit ℂ h).map
    ((Ideal.Quotient.mk (G.incFaceIdeal r)).comp C)

/-- Every higher-overlap quotient element has a denominator that is a power
of the product of newly inverted source coordinates. -/
theorem incidenceRefinement_fraction (y : G.IncFaceRing r) :
    ∃ (n : ℕ) (x : G.IncFaceRing q),
      y * (G.incFaceRefinement h (G.incidenceRefinementDen h))^n =
        G.incFaceRefinement h x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  let χ := G.incFaceRefinement h
  let d := G.incidenceRefinementDen h
  let π := Ideal.Quotient.mk (G.incFaceIdeal r)
  induction p using MvPolynomial.induction_on with
  | C c =>
      obtain ⟨n, a, ha⟩ := faceRefinement_fraction ℂ h c
      refine ⟨n, Ideal.Quotient.mk _ (C a), ?_⟩
      have h := congrArg (fun z => π (C z)) ha
      simpa only [map_mul, map_pow, incidenceRefinementDen, G.incFaceRefinement_C] using h
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
      rw [map_mul, map_mul, G.incFaceRefinement_X]
      calc
        _ = (π p*(χ d)^n)*π (X i) := by ring
        _ = _ := by rw [hx]

/-- Coefficient action induced by the actual quotient restriction. -/
noncomputable abbrev incidenceRefinementAlgebra :
    Algebra (G.IncFaceRing q)
      (G.IncFaceRing r) :=
  (G.incFaceRefinement h).toRingHom.toAlgebra' (fun c x => by
    exact mul_comm ((G.incFaceRefinement h) c) x)

/-- Every actual higher-overlap incidence quotient is localization of its
parent face quotient at the product of newly inverted vertex coordinates. -/
theorem incidenceRefinement_isLocalization :
    letI := G.incidenceRefinementAlgebra h
    IsLocalization.Away (G.incidenceRefinementDen h) (G.IncFaceRing r) := by
  letI := G.incidenceRefinementAlgebra h
  apply IsLocalization.Away.mk
  · exact G.incidenceRefinementDen_isUnit h
  · exact G.incidenceRefinement_fraction h
  · intro x y he
    refine ⟨0, ?_⟩
    simpa only [pow_zero, one_mul] using G.incFaceRefinement_injective h he

end BPFixedPoints.Multigraph
