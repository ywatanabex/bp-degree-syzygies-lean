import BPFixedPoints.Incidence.ProjectiveLineGeometricSections
import BPFixedPoints.Incidence.ProjectiveLineTwistLocallyFree
import BPFixedPoints.Incidence.TwoOpenTwistGlobalSections

/-! # The original polynomial/Laurent matching differential of the actual twist

The actual chart-function coordinate maps are geometric. Their compatibility
with the independently defined polynomial differential uses the actual
open-subscheme restrictions and the original Laurent transition unit.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R]

/-- The original inverse-variable polynomial restriction as an algebra map. -/
noncomputable def inverseLaurentPolynomialMap : Polynomial R →ₐ[R] LaurentPolynomial R :=
  { Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1)) with
    commutes' := by
      intro r
      change Polynomial.eval₂ LaurentPolynomial.C (LaurentPolynomial.T (-1)) (Polynomial.C r) = _
      rw [Polynomial.eval₂_C]
      exact LaurentPolynomial.C_eq_algebraMap r }

/-- The independently specified polynomial/Laurent matching differential for the integral twist. -/
noncomputable def polynomialTwistDifference (n : ℤ) :
    (Polynomial R × Polynomial R) →ₗ[R] LaurentPolynomial R :=
  Polynomial.toLaurentAlg.toLinearMap.comp (LinearMap.fst _ _ _) -
    ((LinearMap.mulRight R (LaurentPolynomial.T n)).comp
      (inverseLaurentPolynomialMap R).toLinearMap).comp (LinearMap.snd _ _ _)

/-- Its formula retains the original two polynomial restrictions and the original Laurent transition. -/
theorem polynomialTwistDifference_apply (n : ℤ) (p : Polynomial R × Polynomial R) :
    polynomialTwistDifference R n p = Polynomial.toLaurent p.1 -
      Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1)) p.2 *
        LaurentPolynomial.T n := rfl

/-- The actual two chart-function coordinates, induced by the original affine scheme isomorphisms. -/
noncomputable def twistChartFunctionCoordinates :
    (Γ((standardOpen R 0).toScheme, ⊤) × Γ((standardOpen R 1).toScheme, ⊤)) ≃+
      (Polynomial R × Polynomial R) :=
  (chartGlobalSectionsEquiv R 0).toAddEquiv.prodCongr (chartGlobalSectionsEquiv R 1).toAddEquiv

/-- The genuine sheaf matching map becomes exactly the original polynomial/Laurent differential. -/
theorem twistChartFunctionCoordinates_difference (n : ℤ)
    (s : Γ((standardOpen R 0).toScheme, ⊤) × Γ((standardOpen R 1).toScheme, ⊤)) :
    standardIntersectionSectionsEquiv R
      (SheafTools.twoOpenGlobalDifference (projectiveLine R) _ _ (twistOverlapUnit R n) s) =
      polynomialTwistDifference R n (twistChartFunctionCoordinates R s) := by
  rw [SheafTools.twoOpenGlobalDifference_apply, map_sub, map_mul,
    left_geometric_sections, right_geometric_sections, twistOverlapUnit_coordinate]
  rfl

end BPFixedPoints.ProjectiveLine
