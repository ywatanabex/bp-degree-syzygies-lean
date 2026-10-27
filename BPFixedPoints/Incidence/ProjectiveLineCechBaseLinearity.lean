import BPFixedPoints.Incidence.OpenUnitBaseLinearity
import BPFixedPoints.Incidence.ProjectiveLineMatchingBaseLinearity
import BPFixedPoints.Incidence.ProjectiveLineCanonicalH1

/-! # Geometric base linearity of the actual overlap frame and state projection

The original frame is the original module projection followed by the inverse
of an actual restriction. Its scalar compatibility is proved before applying
the original Laurent coordinate or coefficient projection.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (R : Type) [CommRing R]

/-- The original left overlap frame is the original chart-coordinate morphism. -/
theorem overlapLeftFrame_eq_chartCoordinates (n : ℤ) :
    (SheafTools.twoOpenTwistOverlapLeftSectionsIso (projectiveLine R) _ _ (twistOverlapUnit R n)).hom =
      SheafTools.openUnitChartCoordinates (projectiveLine R) (standardOpen R 0 ⊓ standardOpen R 1)
        (SheafTools.twoOpenTwistInclusion (projectiveLine R) _ _ (twistOverlapUnit R n) ≫
          biprod.fst ≫ SheafTools.openUnitRestriction (projectiveLine R)
            (show standardOpen R 0 ⊓ standardOpen R 1 ≤ standardOpen R 0 from inf_le_left)) := by
  simp only [SheafTools.twoOpenTwistOverlapLeftSectionsIso, SheafTools.openUnitChartCoordinates,
    Iso.trans_hom, Iso.symm_hom, asIso_hom, Scheme.Modules.Hom.comp_app, Category.assoc]

/-- Actual overlap sections have the original geometric action from the structural projection. -/
@[instance_reducible] noncomputable def twistOverlapBaseModule (n : ℤ) :
    Module R Γ(twistSheaf R n, standardOpen R 0 ⊓ standardOpen R 1) :=
  SchemeTools.schemeBaseOpenModuleSections (toSpecBase R) (twistSheaf R n) _

/-- The original actual overlap frame in Laurent coordinates preserves geometric base scalars. -/
theorem canonicalCechPolynomialOneCoordinates_base_smul (n : ℤ) (r : R)
    (s : Γ(twistSheaf R n, standardOpen R 0 ⊓ standardOpen R 1)) :
    letI := twistOverlapBaseModule R n
    canonicalCechPolynomialOneCoordinates R n (r • s) = r • canonicalCechPolynomialOneCoordinates R n s := by
  letI := twistOverlapBaseModule R n
  letI := SchemeTools.schemeBaseModuleSections (toSpecBase R)
    (SheafTools.openUnitModule (projectiveLine R) (standardOpen R 0 ⊓ standardOpen R 1))
  change standardIntersectionSectionsEquiv R
      ((SheafTools.twoOpenTwistOverlapLeftSectionsIso (projectiveLine R) _ _ (twistOverlapUnit R n)).hom (r • s)) =
    r • standardIntersectionSectionsEquiv R
      ((SheafTools.twoOpenTwistOverlapLeftSectionsIso (projectiveLine R) _ _ (twistOverlapUnit R n)).hom s)
  rw [overlapLeftFrame_eq_chartCoordinates, SchemeTools.openUnitChartCoordinates_base_smul]
  erw [SchemeTools.openUnitModule_base_smul]
  let z : Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤) :=
    SheafTools.openUnitChartCoordinates (projectiveLine R) (standardOpen R 0 ⊓ standardOpen R 1)
      (SheafTools.twoOpenTwistInclusion (projectiveLine R) _ _ (twistOverlapUnit R n) ≫
        biprod.fst ≫ SheafTools.openUnitRestriction (projectiveLine R)
          (show standardOpen R 0 ⊓ standardOpen R 1 ≤ standardOpen R 0 from inf_le_left)) s
  change standardIntersectionSectionsEquiv R
      (SchemeTools.schemeBaseCoefficientHom ((standardOpen R 0 ⊓ standardOpen R 1).ι ≫ toSpecBase R) r * z) =
    r • standardIntersectionSectionsEquiv R z
  rw [map_mul, standardIntersectionSectionsEquiv_coefficient]
  exact (Algebra.smul_def r _).symm

/-- The original actual Laurent overlap coordinates are linear before taking cohomology. -/
noncomputable def canonicalCechPolynomialOneLinearEquiv (n : ℤ) :
    letI := twistOverlapBaseModule R n
    Γ(twistSheaf R n, standardOpen R 0 ⊓ standardOpen R 1) ≃ₗ[R] LaurentPolynomial R := by
  letI := twistOverlapBaseModule R n
  exact { canonicalCechPolynomialOneCoordinates R n with
    map_smul' := canonicalCechPolynomialOneCoordinates_base_smul R n }

/-- Original coefficients of actual overlap sections are linear for the original geometric action. -/
noncomputable def canonicalCechOneLinearEquiv (d : ℕ) :
    letI := twistOverlapBaseModule R (-(d : ℤ))
    Γ(twistSheaf R (-(d : ℤ)), standardOpen R 0 ⊓ standardOpen R 1) ≃ₗ[R] CechLine.C1 R := by
  letI := twistOverlapBaseModule R (-(d : ℤ))
  exact (canonicalCechPolynomialOneLinearEquiv R _).trans (laurentCechCoefficientEquiv R)

/-- The original coefficient state projection on actual overlap sections is geometrically base-linear. -/
noncomputable def canonicalCechProjectionOneLinearMap (d : ℕ) :
    letI := twistOverlapBaseModule R (-(d : ℤ))
    Γ(twistSheaf R (-(d : ℤ)), standardOpen R 0 ⊓ standardOpen R 1) →ₗ[R] CechLine.H1 R d := by
  letI := twistOverlapBaseModule R (-(d : ℤ))
  exact (CechLine.projectionOne R d).comp (canonicalCechOneLinearEquiv R d).toLinearMap

/-- The linear projection retains exactly the original actual coefficient state projection. -/
theorem canonicalCechProjectionOneLinearMap_apply (d : ℕ)
    (s : Γ(twistSheaf R (-(d : ℤ)), standardOpen R 0 ⊓ standardOpen R 1)) :
    letI := twistOverlapBaseModule R (-(d : ℤ))
    canonicalCechProjectionOneLinearMap R d s = canonicalCechProjectionOne R d s := rfl

end BPFixedPoints.ProjectiveLine
