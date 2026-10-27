import BPFixedPoints.Incidence.KoszulFaceInjective
import BPFixedPoints.Incidence.CechRestrictionTorus

/-! # Descend adjacent-chart restrictions to actual incidence quotient rings -/

namespace BPFixedPoints.Multigraph

open MvPolynomial CechProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Restriction from an incidence chart quotient to a one-vertex overlap. -/
noncomputable def incFaceRestriction (σ : V → Bool) (v : V) (b : Bool) :
    G.IncFaceRing (chartFace (Function.update σ v b)) →ₐ[ℂ]
      G.IncFaceRing (overlapFace σ v) :=
  Ideal.Quotient.liftₐ _
    ((Ideal.Quotient.mkₐ ℂ (G.incFaceIdeal (overlapFace σ v))).comp
      (chartPolynomialRestriction ℂ (IncCoeffIdx E) σ v b)) <| by
    intro p hp
    apply G.incFaceToTorus_injective (overlapFace σ v)
    rw [map_zero]
    change G.incFaceAmbientToTorus (overlapFace σ v)
      (chartPolynomialRestriction ℂ (IncCoeffIdx E) σ v b p) = 0
    rw [G.incFaceAmbientToTorus_chartRestriction]
    rw [← G.incFaceToTorus_mk]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

@[simp] theorem incFaceRestriction_mk (σ : V → Bool) (v : V) (b : Bool)
    (p : MvPolynomial (IncCoeffIdx E) (FaceRing ℂ (chartFace (Function.update σ v b)))) :
    G.incFaceRestriction σ v b (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (chartPolynomialRestriction ℂ (IncCoeffIdx E) σ v b p) := rfl

/-- A restricted section and its original chart value agree in the common torus. -/
theorem incFaceToTorus_restriction (σ : V → Bool) (v : V) (b : Bool)
    (x : G.IncFaceRing (chartFace (Function.update σ v b))) :
    G.incFaceToTorus (overlapFace σ v) (G.incFaceRestriction σ v b x) =
      G.incFaceToTorus (chartFace (Function.update σ v b)) x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [G.incFaceRestriction_mk, G.incFaceToTorus_mk, G.incFaceToTorus_mk]
  exact G.incFaceAmbientToTorus_chartRestriction σ v b p

theorem incFaceRestriction_injective (σ : V → Bool) (v : V) (b : Bool) :
    Function.Injective (G.incFaceRestriction σ v b) := by
  intro x y h
  apply G.incFaceToTorus_injective (chartFace (Function.update σ v b))
  simpa only [G.incFaceToTorus_restriction] using
    congrArg (G.incFaceToTorus (overlapFace σ v)) h

end BPFixedPoints.Multigraph
