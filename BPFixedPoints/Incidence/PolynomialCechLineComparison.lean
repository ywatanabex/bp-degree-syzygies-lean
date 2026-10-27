import BPFixedPoints.Incidence.ProjectiveLineTwistCechCoordinates
import BPFixedPoints.Incidence.CechLine

/-! # Original polynomial/Laurent coordinates and the existing coefficient Cech complex

For twist n=-d, the original polynomial differential equals the negative of
the existing right-minus-left Cech differential. This retains the original
monomial exponents and records the degree-one sign explicitly.
-/

namespace BPFixedPoints.ProjectiveLine
open Finsupp AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R]

/-- The original polynomial coefficients give the existing two-chart coefficient module. -/
noncomputable def polynomialCechCoefficientEquiv :
    (Polynomial R × Polynomial R) ≃ₗ[R] CechLine.C0 R :=
  ((Polynomial.toFinsuppIsoAlg R).toLinearEquiv.trans (AddMonoidAlgebra.coeffLinearEquiv R)).prodCongr
    ((Polynomial.toFinsuppIsoAlg R).toLinearEquiv.trans (AddMonoidAlgebra.coeffLinearEquiv R))

/-- Laurent coordinates are the existing Laurent coefficient module with its original scalar action. -/
noncomputable def laurentCechCoefficientEquiv : LaurentPolynomial R ≃ₗ[R] CechLine.C1 R :=
  AddMonoidAlgebra.coeffLinearEquiv R

/-- The actual left polynomial restriction has the original nonnegative exponent formula. -/
theorem polynomial_left_coefficient_formula (p : Polynomial R) :
    laurentCechCoefficientEquiv R (Polynomial.toLaurent p) =
      CechLine.leftRestriction R p.toFinsupp.coeff := rfl

/-- The twisted inverse-variable restriction has exactly the original negative exponent formula. -/
theorem polynomial_right_coefficient_formula (d : ℕ) (p : Polynomial R) :
    laurentCechCoefficientEquiv R
      (inverseLaurentPolynomialMap R p * LaurentPolynomial.T (-(d : ℤ))) =
      CechLine.rightRestriction R d p.toFinsupp.coeff := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, add_mul, map_add, Polynomial.toFinsupp_add, AddMonoidAlgebra.coeff_add, map_add, hp, hq]
  | monomial k r =>
    change (Polynomial.eval₂ LaurentPolynomial.C (LaurentPolynomial.T (-1)) (Polynomial.monomial k r) *
      LaurentPolynomial.T (-(d : ℤ))).coeff = _
    simp only [Polynomial.eval₂_monomial, LaurentPolynomial.T_pow,
      Polynomial.toFinsupp_monomial, AddMonoidAlgebra.coeff_single, CechLine.rightRestriction,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rw [mul_assoc, ← LaurentPolynomial.T_add]
    rw [show (k : ℤ) * (-1) + -(d : ℤ) = -(d : ℤ) - k by omega]
    rw [← LaurentPolynomial.single_eq_C_mul_T]
    rfl

/-- The original polynomial matching map and existing coefficient Cech differential differ only by degree-one negation. -/
theorem polynomialTwistDifference_cech (d : ℕ) (p : Polynomial R × Polynomial R) :
    laurentCechCoefficientEquiv R (polynomialTwistDifference R (-(d : ℤ)) p) =
      -(CechLine.differential R d (polynomialCechCoefficientEquiv R p)) := by
  rw [polynomialTwistDifference_apply]
  change laurentCechCoefficientEquiv R (Polynomial.toLaurent p.1 -
    inverseLaurentPolynomialMap R p.2 * LaurentPolynomial.T (-(d : ℤ))) = _
  rw [map_sub, polynomial_left_coefficient_formula, polynomial_right_coefficient_formula]
  change CechLine.leftRestriction R p.1.toFinsupp.coeff - CechLine.rightRestriction R d p.2.toFinsupp.coeff =
    -(CechLine.rightRestriction R d p.2.toFinsupp.coeff - CechLine.leftRestriction R p.1.toFinsupp.coeff)
  exact (neg_sub _ _).symm

/-- Original chart polynomial coefficients give genuine degree-zero matching coordinates. -/
noncomputable def actualMatchingZeroCoordinates :
    Γ(SheafTools.openUnitModule (projectiveLine R) (standardOpen R 0) ⊞
      SheafTools.openUnitModule (projectiveLine R) (standardOpen R 1), ⊤) ≃+
      CechLine.C0 R :=
  (SheafTools.twoOpenChartPairSectionsEquiv (projectiveLine R) _ _).toAddEquiv.trans
    ((twistChartFunctionCoordinates R).trans (polynomialCechCoefficientEquiv R).toAddEquiv)

/-- The original Laurent coefficient comparison in degree one. -/
noncomputable def actualMatchingOneCoordinates :
    Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤) ≃+ CechLine.C1 R :=
  (standardIntersectionSectionsEquiv R).toAddEquiv.trans (laurentCechCoefficientEquiv R).toAddEquiv

/-- The genuine matching map computes the existing coefficient Cech differential with the explicit degree-one sign. -/
theorem actualMatchingCoordinates_differential (d : ℕ)
    (s : Γ(SheafTools.openUnitModule (projectiveLine R) (standardOpen R 0) ⊞
      SheafTools.openUnitModule (projectiveLine R) (standardOpen R 1), ⊤)) :
    actualMatchingOneCoordinates R
      ((SheafTools.twoOpenTwistDifference (projectiveLine R) _ _
        (twistOverlapUnit R (-(d : ℤ)))).app ⊤ s) =
      -(CechLine.differential R d (actualMatchingZeroCoordinates R s)) := by
  change laurentCechCoefficientEquiv R (standardIntersectionSectionsEquiv R
    ((SheafTools.twoOpenTwistDifference (projectiveLine R) _ _
      (twistOverlapUnit R (-(d : ℤ)))).app ⊤ s)) = _
  rw [← SheafTools.twoOpenChartPairSectionsEquiv_difference,
    twistChartFunctionCoordinates_difference, polynomialTwistDifference_cech]
  rfl

end BPFixedPoints.ProjectiveLine
