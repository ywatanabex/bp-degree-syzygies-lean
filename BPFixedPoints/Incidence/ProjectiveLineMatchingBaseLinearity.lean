import BPFixedPoints.Incidence.ProjectiveLineTwistBaseLinearity

/-! # Original base linearity of the actual matching complex

Both matching terms carry the action induced by the genuine structural
morphism. The actual matching differential and both original coefficient
coordinate comparisons are linear over this independently defined base.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R]

/-- The actual global chart-pair module has the original geometric coefficient action. -/
@[instance_reducible] noncomputable def matchingPairBaseModule :
    Module R Γ(SheafTools.openUnitModule (projectiveLine R) (standardOpen R 0) ⊞
      SheafTools.openUnitModule (projectiveLine R) (standardOpen R 1), ⊤) :=
  SchemeTools.schemeBaseModuleSections (toSpecBase R) _

/-- The actual overlap functions have the coefficient algebra induced by their structural morphism. -/
noncomputable abbrev matchingOverlapBaseAlgebra :
    Algebra R Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤) :=
  SchemeTools.schemeBaseSectionsAlgebra
    ((standardOpen R 0 ⊓ standardOpen R 1).ι ≫ toSpecBase R)

/-- The original actual chart-pair coordinate map is linear over the geometric coefficient ring. -/
noncomputable def matchingPairPolynomialLinearEquiv :
    letI := matchingPairBaseModule R
    Γ(SheafTools.openUnitModule (projectiveLine R) (standardOpen R 0) ⊞
      SheafTools.openUnitModule (projectiveLine R) (standardOpen R 1), ⊤) ≃ₗ[R]
      (Polynomial R × Polynomial R) := by
  letI := matchingPairBaseModule R
  refine { (SheafTools.twoOpenChartPairSectionsEquiv (projectiveLine R) _ _).toAddEquiv.trans
    (twistChartFunctionCoordinates R) with map_smul' := ?_ }
  intro r s
  change twistChartFunctionCoordinates R
    (SheafTools.twoOpenChartPairSectionsEquiv (projectiveLine R) _ _ (r • s)) =
      r • twistChartFunctionCoordinates R
        (SheafTools.twoOpenChartPairSectionsEquiv (projectiveLine R) _ _ s)
  change (chartGlobalSectionsEquiv R 0 _, chartGlobalSectionsEquiv R 1 _) = _
  erw [SheafTools.twoOpenChartPairSectionsEquiv_fst, SheafTools.twoOpenChartPairSectionsEquiv_snd]
  apply Prod.ext
  · change chartGlobalSectionsEquiv R 0 ((biprod.fst :
        SheafTools.openUnitModule (projectiveLine R) (standardOpen R 0) ⊞
          SheafTools.openUnitModule (projectiveLine R) (standardOpen R 1) ⟶
            SheafTools.openUnitModule (projectiveLine R) (standardOpen R 0)).app ⊤ (r • s)) = _
    erw [SchemeTools.openUnitProjection_base_smul]
    erw [map_mul, chartGlobalSectionsEquiv_coefficient]
    change Polynomial.C r * _ = r • chartGlobalSectionsEquiv R 0
      ((SheafTools.twoOpenChartPairSectionsEquiv (projectiveLine R) _ _ s).1)
    rw [SheafTools.twoOpenChartPairSectionsEquiv_fst]
    exact (Algebra.smul_def r _).symm
  · change chartGlobalSectionsEquiv R 1 ((biprod.snd :
        SheafTools.openUnitModule (projectiveLine R) (standardOpen R 0) ⊞
          SheafTools.openUnitModule (projectiveLine R) (standardOpen R 1) ⟶
            SheafTools.openUnitModule (projectiveLine R) (standardOpen R 1)).app ⊤ (r • s)) = _
    erw [SchemeTools.openUnitProjection_base_smul]
    erw [map_mul, chartGlobalSectionsEquiv_coefficient]
    change Polynomial.C r * _ = r • chartGlobalSectionsEquiv R 1
      ((SheafTools.twoOpenChartPairSectionsEquiv (projectiveLine R) _ _ s).2)
    rw [SheafTools.twoOpenChartPairSectionsEquiv_snd]
    exact (Algebra.smul_def r _).symm

/-- The actual degree-zero coefficient comparison is linear for the original geometric base action. -/
noncomputable def actualMatchingZeroLinearEquiv :
    letI := matchingPairBaseModule R
    Γ(SheafTools.openUnitModule (projectiveLine R) (standardOpen R 0) ⊞
      SheafTools.openUnitModule (projectiveLine R) (standardOpen R 1), ⊤) ≃ₗ[R] CechLine.C0 R := by
  letI := matchingPairBaseModule R
  exact (matchingPairPolynomialLinearEquiv R).trans (polynomialCechCoefficientEquiv R)

/-- The actual degree-one coefficient comparison is linear for the original geometric base action. -/
noncomputable def actualMatchingOneLinearEquiv :
    letI := matchingOverlapBaseAlgebra R
    Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤) ≃ₗ[R] CechLine.C1 R := by
  letI := matchingOverlapBaseAlgebra R
  exact (standardIntersectionSectionsAlgEquiv R).toLinearEquiv.trans (laurentCechCoefficientEquiv R)

/-- The genuine matching differential is linear over the independently induced geometric coefficient actions. -/
noncomputable def actualMatchingBaseDifferential (n : ℤ) :
    letI := matchingPairBaseModule R
    letI := matchingOverlapBaseAlgebra R
    Γ(SheafTools.openUnitModule (projectiveLine R) (standardOpen R 0) ⊞
      SheafTools.openUnitModule (projectiveLine R) (standardOpen R 1), ⊤) →ₗ[R]
        Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤) := by
  letI := matchingPairBaseModule R
  letI := matchingOverlapBaseAlgebra R
  refine
    { toFun := (SheafTools.twoOpenTwistDifference (projectiveLine R) _ _ (twistOverlapUnit R n)).app ⊤
      map_add' := fun x y => (SheafTools.twoOpenTwistDifference (projectiveLine R) _ _
        (twistOverlapUnit R n)).val.app (Opposite.op ⊤) |>.hom.map_add x y
      map_smul' := ?_ }
  intro r s
  change _ = Mul.mul (α := Γ((standardOpen R 0 ⊓ standardOpen R 1).toScheme, ⊤))
    (SchemeTools.schemeBaseCoefficientHom
      ((standardOpen R 0 ⊓ standardOpen R 1).ι ≫ toSpecBase R) r) _
  exact SchemeTools.openUnitProjection_base_smul (toSpecBase R) _ _ _ r s

/-- Both base-linear matching coordinates intertwine the genuine differential with the original Cech differential and sign. -/
theorem actualMatchingLinearCoordinates_differential (d : ℕ) :
    letI := matchingPairBaseModule R
    letI := matchingOverlapBaseAlgebra R
    ∀ s, actualMatchingOneLinearEquiv R (actualMatchingBaseDifferential R (-(d : ℤ)) s) =
      -(CechLine.differential R d (actualMatchingZeroLinearEquiv R s)) := by
  letI := matchingPairBaseModule R
  letI := matchingOverlapBaseAlgebra R
  intro s
  exact actualMatchingCoordinates_differential R d s

end BPFixedPoints.ProjectiveLine
