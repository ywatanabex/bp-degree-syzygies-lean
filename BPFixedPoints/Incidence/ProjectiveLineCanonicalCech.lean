import BPFixedPoints.Incidence.TwoOpenTwistCechFrames
import BPFixedPoints.Incidence.PolynomialCechLineComparison

/-! # Polynomial coordinates for the actual twist's canonical Cech complex

The differential here is the ordinary difference of the twist's own
restrictions, independent of the polynomial model. Original chart frames
identify it with the original polynomial/Laurent matching map and hence
the coefficient differential, retaining the degree-one sign.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R]

/-- The actual abelian sheaf of the integral twist on the original projective line. -/
noncomputable def twistAbelianSheaf (n : ℤ) :=
  SheafTools.twoOpenTwistAbelianSheaf (projectiveLine R) _ _ (twistOverlapUnit R n)

/-- Original polynomial coordinates for the actual twist sections on the two charts. -/
noncomputable def canonicalCechPolynomialZeroCoordinates (n : ℤ) :
    (Γ(twistSheaf R n, standardOpen R 0) × Γ(twistSheaf R n, standardOpen R 1)) ≃+
      (Polynomial R × Polynomial R) :=
  ((SheafTools.twoOpenTwistLeftSectionsIso (projectiveLine R) _ _
      (twistOverlapUnit R n)).addCommGroupIsoToAddEquiv.prodCongr
    (SheafTools.twoOpenTwistRightSectionsIso (projectiveLine R) _ _
      (twistOverlapUnit R n)).addCommGroupIsoToAddEquiv).trans (twistChartFunctionCoordinates R)

/-- Original Laurent coordinates for actual overlap twist sections in the left frame. -/
noncomputable def canonicalCechPolynomialOneCoordinates (n : ℤ) :
    Γ(twistSheaf R n, standardOpen R 0 ⊓ standardOpen R 1) ≃+ LaurentPolynomial R :=
  (SheafTools.twoOpenTwistOverlapLeftSectionsIso (projectiveLine R) _ _
    (twistOverlapUnit R n)).addCommGroupIsoToAddEquiv.trans
      (standardIntersectionSectionsEquiv R).toAddEquiv

/-- The canonical Cech differential has exactly the original polynomial/Laurent formula. -/
theorem canonicalCechPolynomialCoordinates_differential (n : ℤ)
    (s : Γ(twistSheaf R n, standardOpen R 0) × Γ(twistSheaf R n, standardOpen R 1)) :
    canonicalCechPolynomialOneCoordinates R n
      (SheafTools.twoOpenSectionDifference (twistAbelianSheaf R n)
        (standardOpen R 0) (standardOpen R 1) s) =
      polynomialTwistDifference R n (canonicalCechPolynomialZeroCoordinates R n s) := by
  have hc := congrArg (standardIntersectionSectionsEquiv R)
    (SheafTools.twoOpenTwistSectionsIso_difference (projectiveLine R) _ _ (twistOverlapUnit R n) s)
  exact hc.trans (twistChartFunctionCoordinates_difference R n _)

/-- Original coefficients of the canonical degree-zero Cech sections. -/
noncomputable def canonicalCechZeroCoordinates (d : ℕ) :
    (Γ(twistSheaf R (-(d : ℤ)), standardOpen R 0) ×
      Γ(twistSheaf R (-(d : ℤ)), standardOpen R 1)) ≃+ CechLine.C0 R :=
  (canonicalCechPolynomialZeroCoordinates R (-(d : ℤ))).trans
    (polynomialCechCoefficientEquiv R).toAddEquiv

/-- Original Laurent coefficients of the canonical degree-one Cech sections. -/
noncomputable def canonicalCechOneCoordinates (d : ℕ) :
    Γ(twistSheaf R (-(d : ℤ)), standardOpen R 0 ⊓ standardOpen R 1) ≃+ CechLine.C1 R :=
  (canonicalCechPolynomialOneCoordinates R (-(d : ℤ))).trans
    (laurentCechCoefficientEquiv R).toAddEquiv

/-- The actual twist's canonical Cech complex has the original coefficient differential and sign. -/
theorem canonicalCechCoordinates_differential (d : ℕ)
    (s : Γ(twistSheaf R (-(d : ℤ)), standardOpen R 0) ×
      Γ(twistSheaf R (-(d : ℤ)), standardOpen R 1)) :
    canonicalCechOneCoordinates R d
      (SheafTools.twoOpenSectionDifference (twistAbelianSheaf R (-(d : ℤ)))
        (standardOpen R 0) (standardOpen R 1) s) =
      -(CechLine.differential R d (canonicalCechZeroCoordinates R d s)) := by
  exact (congrArg (laurentCechCoefficientEquiv R)
    (canonicalCechPolynomialCoordinates_differential R (-(d : ℤ)) s)).trans
      (polynomialTwistDifference_cech R d _)

end BPFixedPoints.ProjectiveLine
