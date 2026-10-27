import BPFixedPoints.Incidence.TwoOpenTwistSheaf
import BPFixedPoints.Incidence.ProjectiveLineOverlap

/-! # Genuine twisted sheaves on Mathlib's actual projective line

The overlap unit is the original Laurent monomial transported by the actual
geometric overlap isomorphism. Its twisted gluing kernel is a genuine sheaf
of modules on Proj. Native local freeness and the original frame transition
are proved in `ProjectiveLineTwistLocallyFree`. The full derived-cohomology
comparison remains a further property.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R]

/-- The actual intersection scheme of the two original standard opens is the Laurent scheme. -/
noncomputable def standardIntersectionLaurentIso :
    (standardOpen R 0 ⊓ standardOpen R 1).toScheme ≅ Spec (CommRingCat.of (LaurentPolynomial R)) :=
  (projectiveLine R).isoOfEq (overlapOpen_eq R).symm ≪≫ overlapOpenIso R 0

/-- Actual overlap global sections in the original Laurent coordinate. -/
noncomputable def standardIntersectionSectionsEquiv :
    Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤) ≃+* LaurentPolynomial R :=
  ((Scheme.Γ.mapIso (standardIntersectionLaurentIso R).op).symm ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial R))).commRingCatIsoToRingEquiv

/-- The original Laurent monomial is an actual unit, with its original inverse monomial. -/
noncomputable def laurentTwistUnit (n : ℤ) : (LaurentPolynomial R)ˣ where
  val := LaurentPolynomial.T n
  inv := LaurentPolynomial.T (-n)
  val_inv := by rw [← LaurentPolynomial.T_add]; simp
  inv_val := by rw [← LaurentPolynomial.T_add]; simp

/-- The original degree-n Laurent transition as a unit of the genuine overlap structure sheaf. -/
noncomputable def twistOverlapUnit (n : ℤ) :
    Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤)ˣ :=
  Units.map (standardIntersectionSectionsEquiv R).symm.toMonoidHom (laurentTwistUnit R n)

/-- The genuine overlap unit has exactly the original Laurent monomial as its coordinate. -/
theorem twistOverlapUnit_coordinate (n : ℤ) :
    standardIntersectionSectionsEquiv R (twistOverlapUnit R n : Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤)) =
      LaurentPolynomial.T n :=
  (standardIntersectionSectionsEquiv R).apply_symm_apply _

/-- Adding the original twists multiplies their actual overlap units. -/
theorem twistOverlapUnit_add (m n : ℤ) :
    twistOverlapUnit R (m+n) = twistOverlapUnit R m * twistOverlapUnit R n := by
  apply Units.ext
  apply (standardIntersectionSectionsEquiv R).injective
  simp only [Units.val_mul, map_mul, twistOverlapUnit_coordinate, LaurentPolynomial.T_add]

/-- The actual opposite twist has exactly the inverse transition unit. -/
theorem twistOverlapUnit_neg (n : ℤ) :
    twistOverlapUnit R (-n) = (twistOverlapUnit R n)⁻¹ := by
  dsimp only [twistOverlapUnit]
  rw [← map_inv]
  apply congrArg (Units.map (standardIntersectionSectionsEquiv R).symm.toMonoidHom)
  apply Units.ext
  rfl

/-- Actual sheaf of `O_Proj`-modules with the original integral Laurent transition. -/
noncomputable def twistSheaf (n : ℤ) : (projectiveLine R).Modules :=
  SheafTools.twoOpenTwistModule (projectiveLine R) (standardOpen R 0) (standardOpen R 1)
    (twistOverlapUnit R n)

end BPFixedPoints.ProjectiveLine
