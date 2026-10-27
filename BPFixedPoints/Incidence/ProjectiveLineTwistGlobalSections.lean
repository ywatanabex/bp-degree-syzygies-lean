import BPFixedPoints.Incidence.ProjectiveLineTwistCechCoordinates
import Mathlib.Algebra.Group.Subgroup.Map

/-! # Actual global twist sections in the original polynomial matching kernel

The comparison uses the actual sheaf kernel and the original geometric
coordinate maps. The geometric coefficient action is not defined by transport.
The comparison in this module is additive; its original geometric base
linearity is proved in `ProjectiveLineTwistBaseLinearity`.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R]

/-- The genuine chart coordinates preserve exactly the matching-kernel condition. -/
theorem twistChartFunctionCoordinates_mem_ker (n : ℤ)
    (s : Γ((standardOpen R 0).toScheme, ⊤) × Γ((standardOpen R 1).toScheme, ⊤)) :
    twistChartFunctionCoordinates R s ∈ LinearMap.ker (polynomialTwistDifference R n) ↔
      s ∈ LinearMap.ker (SheafTools.twoOpenGlobalDifference (projectiveLine R) _ _
        (twistOverlapUnit R n)) := by
  change polynomialTwistDifference R n (twistChartFunctionCoordinates R s) = 0 ↔ _
  rw [← twistChartFunctionCoordinates_difference]
  constructor
  · intro h
    apply (standardIntersectionSectionsEquiv R).injective
    simpa only [map_zero] using h
  · intro h
    change SheafTools.twoOpenGlobalDifference (projectiveLine R) _ _ (twistOverlapUnit R n) s = 0 at h
    rw [h, map_zero]

/-- The actual chart coordinate isomorphism maps precisely the genuine matching kernel to the polynomial kernel. -/
theorem twistChartFunctionCoordinates_map_ker (n : ℤ) :
    (LinearMap.ker (SheafTools.twoOpenGlobalDifference (projectiveLine R) _ _
      (twistOverlapUnit R n))).toAddSubgroup.map (twistChartFunctionCoordinates R).toAddMonoidHom =
      (LinearMap.ker (polynomialTwistDifference R n)).toAddSubgroup := by
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (twistChartFunctionCoordinates_mem_ker R n s).mpr hs
  · intro hp
    change p ∈ LinearMap.ker (polynomialTwistDifference R n) at hp
    refine ⟨(twistChartFunctionCoordinates R).symm p, ?_,
      (twistChartFunctionCoordinates R).apply_symm_apply p⟩
    apply (twistChartFunctionCoordinates_mem_ker R n _).mp
    simpa only [AddEquiv.apply_symm_apply] using hp

/-- The actual chart coordinate isomorphism restricted to the original matching kernels. -/
noncomputable def twistChartKernelCoordinates (n : ℤ) :
    LinearMap.ker (SheafTools.twoOpenGlobalDifference (projectiveLine R) _ _
      (twistOverlapUnit R n)) ≃+ LinearMap.ker (polynomialTwistDifference R n) :=
  ((twistChartFunctionCoordinates R).addSubgroupMap _).trans
    (AddEquiv.addSubgroupCongr (twistChartFunctionCoordinates_map_ker R n))

/-- All genuine global twist sections equal all original polynomial matching pairs. -/
noncomputable def twistSheafGlobalSectionsPolynomialEquiv (n : ℤ) :
    Γ(twistSheaf R n, ⊤) ≃+ LinearMap.ker (polynomialTwistDifference R n) :=
  (SheafTools.twoOpenTwistGlobalSectionsEquiv (projectiveLine R) _ _
    (twistOverlapUnit R n)).toAddEquiv.trans (twistChartKernelCoordinates R n)

/-- The comparison retains the original actual chart projections in their geometric polynomial coordinates. -/
theorem twistSheafGlobalSectionsPolynomialEquiv_val (n : ℤ) (s : Γ(twistSheaf R n, ⊤)) :
    (twistSheafGlobalSectionsPolynomialEquiv R n s).val =
      (chartGlobalSectionsEquiv R 0
        ((SheafTools.twoOpenTwistInclusion (projectiveLine R) _ _ (twistOverlapUnit R n) ≫ biprod.fst).app ⊤ s),
       chartGlobalSectionsEquiv R 1
        ((SheafTools.twoOpenTwistInclusion (projectiveLine R) _ _ (twistOverlapUnit R n) ≫ biprod.snd).app ⊤ s)) := by
  change twistChartFunctionCoordinates R
    (SheafTools.twoOpenTwistGlobalSectionsEquiv (projectiveLine R) _ _ (twistOverlapUnit R n) s).val = _
  change (chartGlobalSectionsEquiv R 0 _, chartGlobalSectionsEquiv R 1 _) = _
  rw [SheafTools.twoOpenTwistGlobalSectionsEquiv_left, SheafTools.twoOpenTwistGlobalSectionsEquiv_right]

/-- Existence form of the actual polynomial-kernel comparison, with no higher-vanishing hypothesis. -/
theorem twistSheafGlobalSectionsPolynomial_comparison (n : ℤ) :
    Nonempty (Γ(twistSheaf R n, ⊤) ≃+ LinearMap.ker (polynomialTwistDifference R n)) :=
  ⟨twistSheafGlobalSectionsPolynomialEquiv R n⟩

end BPFixedPoints.ProjectiveLine
