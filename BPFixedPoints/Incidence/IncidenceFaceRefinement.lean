import BPFixedPoints.Incidence.CechFaceRefinement
import BPFixedPoints.Incidence.KoszulFaceRestriction

/-! # Compatible restrictions among all incidence faces

These maps act on the original incidence quotient rings. Their compatibility is
proved by evaluation in the common torus, whose face maps are injective.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial CechProduct IncidenceLaurent

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

theorem incFaceVertexUnit_orientation (q : V → Fin 3) (v : V) :
    G.incFaceVertexUnit q v =
      if q v = 1 then (G.incFaceVertexUnit (fun _ => 0) v)⁻¹
      else G.incFaceVertexUnit (fun _ => 0) v := by
  apply Units.ext
  by_cases h : q v = 1 <;>
    simp [incFaceVertexUnit, incChartVertexUnit, incChartVal, faceOrientation, h]

/-- Refinement preserves the actual torus monomial, including inverted coordinates. -/
theorem unitMonomial_faceRefinement {q r : V → Fin 3} (h : FaceRefines q r)
    (m : FaceMonoid q) :
    unitMonomial (G.incFaceVertexUnit r)
        (Multiplicative.ofAdd (faceToInt r (refinementExponent h m))) =
      unitMonomial (G.incFaceVertexUnit q) (Multiplicative.ofAdd (faceToInt q m)) := by
  change (∏ v, G.incFaceVertexUnit r v ^
      exponentToInt (r v) (refinementCoordinate (h v) (m v))) =
    ∏ v, G.incFaceVertexUnit q v ^ exponentToInt (q v) (m v)
  apply Finset.prod_congr rfl
  intro v _
  rw [G.incFaceVertexUnit_orientation r, G.incFaceVertexUnit_orientation q]
  exact refinementCoordinate_unit _ (h v) (m v)

theorem faceEvaluate_refinement {q r : V → Fin 3} (h : FaceRefines q r)
    (x : FaceRing ℂ q) :
    faceEvaluate r (G.incFaceVertexUnit r) (faceRefinementMap ℂ h x) =
      faceEvaluate q (G.incFaceVertexUnit q) x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m c =>
    rw [faceRefinementMap_single, faceEvaluate_single, faceEvaluate_single,
      G.unitMonomial_faceRefinement]

theorem incFaceAmbientToTorus_refinement {q r : V → Fin 3} (h : FaceRefines q r)
    (p : MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)) :
    G.incFaceAmbientToTorus r (facePolynomialRefinement ℂ (IncCoeffIdx E) h p) =
      G.incFaceAmbientToTorus q p := by
  have he : (G.incFaceAmbientToTorus r).comp
      (facePolynomialRefinement ℂ (IncCoeffIdx E) h) = G.incFaceAmbientToTorus q := by
    apply MvPolynomial.algHom_ext'
    · apply AlgHom.ext
      intro c
      change G.incFaceAmbientToTorus r
        (facePolynomialRefinement ℂ (IncCoeffIdx E) h (C c)) =
          G.incFaceAmbientToTorus q (C c)
      simp [incFaceAmbientToTorus, facePolynomialRefinement, G.faceEvaluate_refinement]
    · intro c
      simp [incFaceAmbientToTorus, facePolynomialRefinement]
  exact AlgHom.congr_fun he p

/-- Restriction from any incidence face to a higher intersection. -/
noncomputable def incFaceRefinement {q r : V → Fin 3} (h : FaceRefines q r) :
    G.IncFaceRing q →ₐ[ℂ] G.IncFaceRing r :=
  Ideal.Quotient.liftₐ _
    ((Ideal.Quotient.mkₐ ℂ (G.incFaceIdeal r)).comp
      (facePolynomialRefinement ℂ (IncCoeffIdx E) h)) <| by
    intro p hp
    apply G.incFaceToTorus_injective r
    rw [map_zero]
    change G.incFaceAmbientToTorus r (facePolynomialRefinement ℂ (IncCoeffIdx E) h p) = 0
    rw [G.incFaceAmbientToTorus_refinement, ← G.incFaceToTorus_mk]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

@[simp] theorem incFaceRefinement_mk {q r : V → Fin 3} (h : FaceRefines q r)
    (p : MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)) :
    G.incFaceRefinement h (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (facePolynomialRefinement ℂ (IncCoeffIdx E) h p) := rfl

/-- Every face restriction commutes with the fixed embedding in the original torus. -/
theorem incFaceToTorus_refinement {q r : V → Fin 3} (h : FaceRefines q r)
    (x : G.IncFaceRing q) :
    G.incFaceToTorus r (G.incFaceRefinement h x) = G.incFaceToTorus q x := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact G.incFaceAmbientToTorus_refinement h p

theorem incFaceRefinement_injective {q r : V → Fin 3} (h : FaceRefines q r) :
    Function.Injective (G.incFaceRefinement h) := by
  intro x y hxy
  apply G.incFaceToTorus_injective q
  simpa only [G.incFaceToTorus_refinement] using congrArg (G.incFaceToTorus r) hxy

@[simp] theorem incFaceRefinement_refl (q : V → Fin 3) :
    G.incFaceRefinement (faceRefines_refl q) = AlgHom.id ℂ (G.IncFaceRing q) := by
  ext x
  apply G.incFaceToTorus_injective q
  exact G.incFaceToTorus_refinement (faceRefines_refl q) x

/-- All multiple-overlap restrictions satisfy the cocycle identity as actual ring maps. -/
theorem incFaceRefinement_comp {q r s : V → Fin 3}
    (hqr : FaceRefines q r) (hrs : FaceRefines r s) :
    (G.incFaceRefinement hrs).comp (G.incFaceRefinement hqr) =
      G.incFaceRefinement (faceRefines_trans hqr hrs) := by
  ext x
  apply G.incFaceToTorus_injective s
  simp only [AlgHom.comp_apply, G.incFaceToTorus_refinement]

/-- The old adjacent restriction is a special case of the full face diagram. -/
theorem incFaceRefinement_eq_adjacent (σ : V → Bool) (v : V) (b : Bool)
    (h : FaceRefines (chartFace (Function.update σ v b)) (overlapFace σ v)) :
    G.incFaceRefinement h = G.incFaceRestriction σ v b := by
  ext x
  apply G.incFaceToTorus_injective (overlapFace σ v)
  rw [G.incFaceToTorus_refinement, G.incFaceToTorus_restriction]

end BPFixedPoints.Multigraph
