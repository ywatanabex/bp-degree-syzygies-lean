import BPFixedPoints.Incidence.ProjectiveLineOverlap

/-! # Genuine structure-sheaf restrictions in projective-line coordinates

The actual Proj structure sheaf has the original polynomial charts and Laurent
overlap. Its two restriction maps are the usual inclusion and inversion maps,
by Mathlib's homogeneous-localization restriction theorem.
-/

namespace BPFixedPoints.ProjectiveLine
open MvPolynomial AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R]

/-- Actual functions on either standard Proj open, in polynomial coordinates. -/
noncomputable def chartSectionsEquiv (i : Fin 2) :
    Γ(projectiveLine R, standardOpen R i) ≃+* Polynomial R :=
  (Proj.basicOpenIsoAway (grading R) (X i) (isHomogeneous_X R i)
    (by decide)).symm.commRingCatIsoToRingEquiv.trans (chartEquiv R i)

/-- Actual functions on the genuine overlap, in the left Laurent coordinate. -/
noncomputable def overlapSectionsEquiv :
    Γ(projectiveLine R, overlapOpen R) ≃+* LaurentPolynomial R :=
  (Proj.basicOpenIsoAway (grading R) (X (0 : Fin 2) * X 1)
    ((isHomogeneous_X R 0).mul (isHomogeneous_X R 1))
    (by decide)).symm.commRingCatIsoToRingEquiv.trans (overlapEquiv R 0)

/-- The Laurent section coordinate retains the original homogeneous section map. -/
theorem overlapSectionsEquiv_away (a : OverlapRing R) :
    overlapSectionsEquiv R
      ((Proj.basicOpenIsoAway (grading R) (X (0 : Fin 2) * X 1)
        ((isHomogeneous_X R 0).mul (isHomogeneous_X R 1)) (by decide)).hom a) =
      overlapEquiv R 0 a :=
  congrArg (overlapEquiv R 0)
    ((Proj.basicOpenIsoAway (grading R) (X (0 : Fin 2) * X 1)
      ((isHomogeneous_X R 0).mul (isHomogeneous_X R 1))
      (by decide)).commRingCatIsoToRingEquiv.symm_apply_apply a)

theorem overlap_le_standard (i : Fin 2) : overlapOpen R ≤ standardOpen R i := by
  rw [overlapOpen_eq]
  fin_cases i
  · exact inf_le_left
  · exact inf_le_right

/-- The actual structure-sheaf restriction is the original homogeneous restriction. -/
theorem homogeneous_sections_restrict (i : Fin 2) (a : ChartRing R i) :
    (projectiveLine R).presheaf.map (homOfLE (overlap_le_standard R i)).op
      ((Proj.basicOpenIsoAway (grading R) (X i) (isHomogeneous_X R i) (by decide)).hom a) =
    (Proj.basicOpenIsoAway (grading R) (X (0 : Fin 2) * X 1)
      ((isHomogeneous_X R 0).mul (isHomogeneous_X R 1)) (by decide)).hom
        (overlapMap R i a) := by
  have hx : (X 0 * X 1 : CoxRing R) = X i * X i.rev := by
    fin_cases i <;> simp [mul_comm]
  exact (ConcreteCategory.congr_hom
    (Proj.awayMap_awayToSection (grading R) (isHomogeneous_X R i.rev) hx) a).symm

/-- Restriction from the actual left Proj open is the original Laurent inclusion. -/
theorem left_sections_restrict (p : Polynomial R) :
    overlapSectionsEquiv R
      ((projectiveLine R).presheaf.map (homOfLE (overlap_le_standard R 0)).op
        ((chartSectionsEquiv R 0).symm p)) = Polynomial.toLaurent p := by
  have h := homogeneous_sections_restrict R 0 (fromPolynomial R 0 p)
  calc
    _ = overlapSectionsEquiv R
        ((Proj.basicOpenIsoAway (grading R) (X (0 : Fin 2) * X 1)
          ((isHomogeneous_X R 0).mul (isHomogeneous_X R 1)) (by decide)).hom
            (overlapMap R 0 (fromPolynomial R 0 p))) := congrArg (overlapSectionsEquiv R) h
    _ = overlapEquiv R 0 (overlapMap R 0 (fromPolynomial R 0 p)) :=
      overlapSectionsEquiv_away R _
    _ = _ := overlapEquiv_left_polynomial R p

/-- Restriction from the actual right Proj open inverts the Laurent parameter. -/
theorem right_sections_restrict (p : Polynomial R) :
    overlapSectionsEquiv R
      ((projectiveLine R).presheaf.map (homOfLE (overlap_le_standard R 1)).op
        ((chartSectionsEquiv R 1).symm p)) =
      Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1)) p := by
  have h := homogeneous_sections_restrict R 1 (fromPolynomial R 1 p)
  calc
    _ = overlapSectionsEquiv R
        ((Proj.basicOpenIsoAway (grading R) (X (0 : Fin 2) * X 1)
          ((isHomogeneous_X R 0).mul (isHomogeneous_X R 1)) (by decide)).hom
            (overlapMap R 1 (fromPolynomial R 1 p))) := congrArg (overlapSectionsEquiv R) h
    _ = overlapEquiv R 0 (overlapMap R 1 (fromPolynomial R 1 p)) :=
      overlapSectionsEquiv_away R _
    _ = _ := overlapEquiv_right_polynomial R p

end BPFixedPoints.ProjectiveLine
