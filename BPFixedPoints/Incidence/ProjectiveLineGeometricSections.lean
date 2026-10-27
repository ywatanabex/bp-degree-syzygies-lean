import BPFixedPoints.Incidence.ProjectiveLineTwistSheaf
import BPFixedPoints.Incidence.ProjectiveLineTransitionMorphisms
import BPFixedPoints.Incidence.AffineSchemeGlobalSections

/-! # Actual global sections of the projective charts in geometric coordinates

The coordinate equivalences are induced by the actual affine scheme
isomorphisms. The original Laurent chart morphisms identify the genuine
open-subscheme restrictions with polynomial inclusion and inversion.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R]

/-- The original polynomial chart inclusion is the inverse of the actual affine chart isomorphism. -/
theorem standardOpenIso_inv_ι (i : Fin 2) :
    (standardOpenIso R i).inv ≫ (standardOpen R i).ι = chartι R i := by
  dsimp only [standardOpenIso, chartι, Proj.awayι, Iso.trans_inv]
  rw [Category.assoc]
  rfl

/-- The original Laurent inclusion is the inverse of the actual intersection isomorphism. -/
theorem standardIntersectionLaurentIso_inv_ι :
    (standardIntersectionLaurentIso R).inv ≫ (standardOpen R 0 ⊓ standardOpen R 1).ι =
      overlapι R := by
  dsimp only [standardIntersectionLaurentIso, Iso.trans_inv]
  rw [Category.assoc, Scheme.isoOfEq_inv_ι]
  dsimp only [overlapOpenIso, overlapι, Proj.awayι, Iso.trans_inv]
  rw [Category.assoc]
  rfl

/-- The actual restriction from the left standard open has the original polynomial Laurent map. -/
theorem left_geometric_restriction :
    (projectiveLine R).homOfLE (show standardOpen R 0 ⊓ standardOpen R 1 ≤ standardOpen R 0 from inf_le_left) ≫
      (standardOpenIso R 0).hom =
    (standardIntersectionLaurentIso R).hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R)) := by
  apply (cancel_mono ((standardOpenIso R 0).inv ≫ (standardOpen R 0).ι)).mp
  rw [Category.assoc, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]
  rw [standardOpenIso_inv_ι, Category.assoc, left_overlap_chart, ← standardIntersectionLaurentIso_inv_ι, Iso.hom_inv_id_assoc]

/-- The actual restriction from the right standard open has the original inverse-variable map. -/
theorem right_geometric_restriction :
    (projectiveLine R).homOfLE (show standardOpen R 0 ⊓ standardOpen R 1 ≤ standardOpen R 1 from inf_le_right) ≫
      (standardOpenIso R 1).hom =
    (standardIntersectionLaurentIso R).hom ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1)) :
          Polynomial R →+* LaurentPolynomial R)) := by
  apply (cancel_mono ((standardOpenIso R 1).inv ≫ (standardOpen R 1).ι)).mp
  rw [Category.assoc, Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]
  rw [standardOpenIso_inv_ι, Category.assoc, right_overlap_chart, ← standardIntersectionLaurentIso_inv_ι, Iso.hom_inv_id_assoc]

/-- Actual global functions on either standard open in its original geometric polynomial chart. -/
noncomputable def chartGlobalSectionsEquiv (i : Fin 2) :
    Γ((standardOpen R i).toScheme, ⊤) ≃+* Polynomial R :=
  (SchemeTools.affineIsoSectionsIso (standardOpenIso R i)).commRingCatIsoToRingEquiv

/-- Genuine left open-subscheme restriction has exactly the original Laurent polynomial formula. -/
theorem left_geometric_sections (s : Γ((standardOpen R 0).toScheme, ⊤)) :
    standardIntersectionSectionsEquiv R
      (((projectiveLine R).homOfLE
        (show standardOpen R 0 ⊓ standardOpen R 1 ≤ standardOpen R 0 from inf_le_left)).appTop s) =
      Polynomial.toLaurent (chartGlobalSectionsEquiv R 0 s) :=
  ConcreteCategory.congr_hom (SchemeTools.affineIsoSectionsIso_naturality
    (standardIntersectionLaurentIso R) (standardOpenIso R 0) _ _
    (left_geometric_restriction R)) s

/-- Genuine right open-subscheme restriction has exactly the original inverse-variable formula. -/
theorem right_geometric_sections (s : Γ((standardOpen R 1).toScheme, ⊤)) :
    standardIntersectionSectionsEquiv R
      (((projectiveLine R).homOfLE
        (show standardOpen R 0 ⊓ standardOpen R 1 ≤ standardOpen R 1 from inf_le_right)).appTop s) =
      Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1))
        (chartGlobalSectionsEquiv R 1 s) :=
  ConcreteCategory.congr_hom (SchemeTools.affineIsoSectionsIso_naturality
    (standardIntersectionLaurentIso R) (standardOpenIso R 1) _ _
    (right_geometric_restriction R)) s

end BPFixedPoints.ProjectiveLine
