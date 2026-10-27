import BPFixedPoints.Incidence.BinaryCoverNativeCohomology
import BPFixedPoints.Incidence.VertexProjectiveTwistCohomologyCup

/-! # All integral vertex twists retain their actual native Ext roofs

The original native roof gives the map. Its comparison with the original
Yoneda map supplies linearity for the independently specified geometric
actions. No action or product is transported from state coordinates.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory TopologicalSpace
open SheafTools.BinaryCells SchemeTools ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]
local instance vertexNativeAllHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _

/-- The original native augmentation roof on the original vertex cell Hom quotient in every degree. -/
abbrev vertexTwistNativeComparison (a : V → ℤ) (n : ℕ) :
    vertexTwistCellCohomologyAt R V a n →+ Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) n :=
  nativeCubicalComparison (vertexCoordinateOpen R V) (vertexTwistAbelianSheaf R V a)
    (vertexCellChartOpen_cover R V) n

/-- The native degree-zero roof is the original geometric linear comparison over every small commutative base ring. -/
theorem vertexTwistNativeComparison_zero (a : V → ℤ)
    (x : vertexTwistCellCohomologyAt R V a 0) :
    vertexTwistNativeComparison R V a 0 x = vertexTwistCellActualZeroLinearEquiv R V a x :=
  nativeCubicalComparison_zero _ _ _ x

/-- The native degree-zero map is bijective without a Noetherian or relative term acyclicity hypothesis. -/
theorem vertexTwistNativeComparison_zero_bijective (a : V → ℤ) :
    Function.Bijective (vertexTwistNativeComparison R V a 0) := by
  have h : (vertexTwistNativeComparison R V a 0 : vertexTwistCellCohomologyAt R V a 0 →
      Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) 0) = vertexTwistCellActualZeroLinearEquiv R V a := by
    funext x
    exact vertexTwistNativeComparison_zero R V a x
  rw [h]
  exact (vertexTwistCellActualZeroLinearEquiv R V a).bijective

variable [IsNoetherianRing R]

/-- Every integral twist and every degree retain the original geometric Yoneda comparison and its actual accumulated native cone sign. -/
theorem vertexTwistNativeComparison_yoneda (a : V → ℤ) (n : ℕ)
    (x : vertexTwistCellCohomologyAt R V a n) :
    vertexTwistNativeComparison R V a n x =
      nativeYonedaSign n • vertexTwistCellActualAtLinearEquiv R V a n x :=
  nativeCubicalComparison_yoneda _ _ _ (vertexTwistCellSheaf_terms_acyclic R V a) n x

/-- The independently specified original native roof is a linear equivalence in every degree for the original geometric base actions. -/
def vertexTwistNativeLinearEquiv (a : V → ℤ) (n : ℕ) :
    letI := vertexTwistCellAtModule R V a n
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) n) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) n
    vertexTwistCellCohomologyAt R V a n ≃ₗ[R] Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) n := by
  letI := vertexTwistCellAtModule R V a n
  letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) n) :=
    schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) n
  let e := AddEquiv.ofBijective (vertexTwistNativeComparison R V a n)
    (nativeCubicalComparison_bijective _ _ _ (vertexTwistCellSheaf_terms_acyclic R V a) n)
  refine e.toLinearEquiv ?_
  intro r x
  change vertexTwistNativeComparison R V a n (r • x) = r • vertexTwistNativeComparison R V a n x
  rw [vertexTwistNativeComparison_yoneda,vertexTwistNativeComparison_yoneda,map_smul]
  exact smul_comm _ _ _

/-- The all-degree linear equivalence retains the native augmentation roof itself on every original class. -/
theorem vertexTwistNativeLinearEquiv_apply (a : V → ℤ) (n : ℕ)
    (x : vertexTwistCellCohomologyAt R V a n) :
    vertexTwistNativeLinearEquiv R V a n x = vertexTwistNativeComparison R V a n x := rfl

/-- The actual native sign on every original class has triangular exponent. -/
theorem vertexTwistNativeComparison_triangular (a : V → ℤ) (n : ℕ)
    (x : vertexTwistCellCohomologyAt R V a n) :
    vertexTwistNativeComparison R V a n x =
      ((n*(n+1)/2 : ℕ) : ℤ).negOnePow • vertexTwistCellActualAtLinearEquiv R V a n x := by
  rw [vertexTwistNativeComparison_yoneda,nativeYonedaSign_eq]

end
end BPFixedPoints.ProjectiveLine
