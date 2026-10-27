import BPFixedPoints.Incidence.ProjectiveLineOverlap
import BPFixedPoints.Incidence.ProjectiveLineOverBase

/-! # Original coordinate inversion as a genuine Proj morphism equality

The two original Laurent restrictions land in the same actual Proj overlap.
The equality is proved using Mathlib's homogeneous-localization morphisms,
and retains the original common-base coefficient map.
-/

namespace BPFixedPoints.ProjectiveLine
open MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R]

/-- The actual Laurent chart inclusion into the independently defined Proj line. -/
noncomputable def overlapι :
    Spec (CommRingCat.of (LaurentPolynomial R)) ⟶ projectiveLine R :=
  Spec.map (overlapEquiv R 0).toCommRingCatIso.hom ≫
    Proj.awayι (grading R) (X (0 : Fin 2) * X 1)
      ((isHomogeneous_X R 0).mul (isHomogeneous_X R 1)) (by decide)

instance overlapι_isOpenImmersion : IsOpenImmersion (overlapι R) := by
  dsimp only [overlapι]
  infer_instance

theorem overlapι_opensRange : (overlapι R).opensRange = overlapOpen R := by
  dsimp only [overlapι]
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]
  rfl

/-- Both original homogeneous restrictions induce the same actual overlap inclusion. -/
theorem homogeneous_overlap_chart (i : Fin 2) :
    Spec.map (overlapEquiv R 0).toCommRingCatIso.hom ≫
        Spec.map (CommRingCat.ofHom (overlapMap R i)) ≫
          Proj.awayι (grading R) (X i) (isHomogeneous_X R i) (by decide) = overlapι R := by
  have hx : (X 0 * X 1 : CoxRing R) = X i * X i.rev := by
    fin_cases i <;> simp [mul_comm]
  exact congrArg
    (fun f => Spec.map (overlapEquiv R 0).toCommRingCatIso.hom ≫ f)
    (Proj.SpecMap_awayMap_awayι (grading R) (isHomogeneous_X R i) (by decide)
      (isHomogeneous_X R i.rev) hx)

/-- The original left Laurent restriction is the genuine Proj overlap morphism. -/
@[reassoc] theorem left_overlap_chart :
    Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R)) ≫
      chartι R 0 = overlapι R := by
  have h : (chartEquiv R 0).toCommRingCatIso.hom ≫
      CommRingCat.ofHom (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R) =
      CommRingCat.ofHom (overlapMap R 0) ≫ (overlapEquiv R 0).toCommRingCatIso.hom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (overlapEquiv_map R 0 a).symm
  dsimp only [chartι]
  rw [← Spec.map_comp_assoc, h, Spec.map_comp_assoc]
  exact homogeneous_overlap_chart R 0

/-- The original right inverse-variable restriction is the same genuine Proj overlap morphism. -/
@[reassoc] theorem right_overlap_chart :
    Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1)) :
        Polynomial R →+* LaurentPolynomial R)) ≫ chartι R 1 = overlapι R := by
  have h : (chartEquiv R 1).toCommRingCatIso.hom ≫
      CommRingCat.ofHom (Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1))) =
      CommRingCat.ofHom (overlapMap R 1) ≫ (overlapEquiv R 0).toCommRingCatIso.hom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    have he := congrArg (fun z => overlapEquiv R 0 (overlapMap R 1 z))
      (fromPolynomial_toPolynomial R 1 a)
    exact ((he.symm).trans (overlapEquiv_right_polynomial R (toPolynomial R 1 a))).symm
  dsimp only [chartι]
  rw [← Spec.map_comp_assoc, h, Spec.map_comp_assoc]
  exact homogeneous_overlap_chart R 1

/-- Coordinate inversion identifies the two actual morphisms into Proj. -/
theorem left_right_transition :
    Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R)) ≫
        chartι R 0 =
      Spec.map (CommRingCat.ofHom
        (Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1)) :
          Polynomial R →+* LaurentPolynomial R)) ≫ chartι R 1 :=
  (left_overlap_chart R).trans (right_overlap_chart R).symm

/-- The actual overlap inclusion preserves the original Laurent coefficient map. -/
@[reassoc] theorem overlapι_toSpecBase :
    overlapι R ≫ toSpecBase R =
      Spec.map (CommRingCat.ofHom (algebraMap R (LaurentPolynomial R))) := by
  rw [← left_overlap_chart, Category.assoc, chartι_toSpecBase, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact Polynomial.toLaurent_C r

end BPFixedPoints.ProjectiveLine
