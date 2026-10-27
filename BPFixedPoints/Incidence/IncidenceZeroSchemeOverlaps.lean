import BPFixedPoints.Incidence.IncidenceZeroIdealDescent
import BPFixedPoints.Incidence.QuotientZeroLocusPullback
import BPFixedPoints.Incidence.IncidenceFaceDiagram
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Actual affine zero-scheme comparison on every projective face overlap

The original incidence face scheme is the genuine closed zero subscheme of
its ambient polynomial/Laurent coefficient chart. Every overlap square is an
actual scheme pullback, from equality of the original extended zero ideals.
This supplies local descent data without assuming an ambient projective scheme.
-/

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory CechProduct SchemeTools
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Ambient coefficient chart before imposing any homogeneous incidence equation. -/
noncomputable def incidenceAmbientFace (_G : Multigraph V E) (q : V → Fin 3) : Scheme :=
  Spec (CommRingCat.of (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)))

/-- Ambient face restriction, keeping all universal coefficient variables. -/
noncomputable def incidenceAmbientFaceMap {q r : V → Fin 3} (h : FaceRefines q r) :
    G.incidenceAmbientFace r ⟶ G.incidenceAmbientFace q :=
  Spec.map (CommRingCat.ofHom (facePolynomialRefinement ℂ (IncCoeffIdx E) h).toRingHom)

/-- The actual quotient inclusion of the original incidence zero scheme on a face. -/
noncomputable def incidenceZeroFaceι (q : V → Fin 3) :
    G.incidenceAffineFace q ⟶ G.incidenceAmbientFace q :=
  Spec.map (CommRingCat.ofHom (R := MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q))
        (S := G.IncFaceRing q) (Ideal.Quotient.mk (G.incFaceIdeal q)))

instance incidenceZeroFaceι_isClosedImmersion (q : V → Fin 3) :
    IsClosedImmersion (G.incidenceZeroFaceι q) :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (R := MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q))
      (S := G.IncFaceRing q) (Ideal.Quotient.mk (G.incFaceIdeal q))) Ideal.Quotient.mk_surjective

/-- The quotient-ring square commutes for the original face maps. -/
theorem incidenceZeroFace_square {q r : V → Fin 3} (h : FaceRefines q r) :
    CommRingCat.ofHom (facePolynomialRefinement ℂ (IncCoeffIdx E) h).toRingHom ≫
        CommRingCat.ofHom (R := MvPolynomial (IncCoeffIdx E) (FaceRing ℂ r))
        (S := G.IncFaceRing r) (Ideal.Quotient.mk (G.incFaceIdeal r)) =
      CommRingCat.ofHom (R := MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q))
        (S := G.IncFaceRing q) (Ideal.Quotient.mk (G.incFaceIdeal q)) ≫
        CommRingCat.ofHom (R := G.IncFaceRing q) (S := G.IncFaceRing r) (G.incFaceRefinement h).toRingHom := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact (G.incFaceRefinement_mk h p).symm

/-- Genuine scheme-theoretic base change of the original closed zero loci on
all mixed polynomial/Laurent overlaps, including boundary points. -/
theorem incidenceZeroFace_isPullback {q r : V → Fin 3} (h : FaceRefines q r) :
    IsPullback (G.incidenceZeroFaceι r) (G.incidenceFaceMap h)
      (G.incidenceAmbientFaceMap h) (G.incidenceZeroFaceι q) :=
  quotientSquare_isPullback
    (CommRingCat.of (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)))
    (CommRingCat.of (MvPolynomial (IncCoeffIdx E) (FaceRing ℂ r)))
    (CommRingCat.ofHom (facePolynomialRefinement ℂ (IncCoeffIdx E) h).toRingHom)
    (G.incFaceIdeal q) (G.incFaceIdeal r) (G.incFaceIdeal_map_refinement h).symm
    (CommRingCat.ofHom (R := G.IncFaceRing q) (S := G.IncFaceRing r) (G.incFaceRefinement h).toRingHom) (G.incidenceZeroFace_square h)

end BPFixedPoints.Multigraph
