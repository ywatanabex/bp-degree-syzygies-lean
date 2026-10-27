import BPFixedPoints.Incidence.BinaryCoverNativeFirstCohomology
import BPFixedPoints.Incidence.VertexProjectiveTwistCellCohomology

/-! # Native first cohomology comparison for the original integral vertex twists

The native map is fixed by its original augmentation roof. Its linearity
and bijectivity use the proved comparison with the original Yoneda map,
for the independently specified geometric actions on both sides.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory TopologicalSpace
open SheafTools.BinaryCells SchemeTools ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

local instance vertexNativeFirstHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _

/-- The original native first cubical augmentation roof for the actual integral twist. -/
abbrev vertexTwistNativeFirstComparison (a : V → ℤ) :
    vertexTwistCellCohomology R V a 0 →+ Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) 1 :=
  nativeCubicalFirstComparison (vertexCoordinateOpen R V) (vertexTwistAbelianSheaf R V a)
    (vertexCellChartOpen_cover R V)

variable [IsNoetherianRing R]

/-- The native first roof equals the negative original geometric linear comparison on every original quotient class. -/
theorem vertexTwistNativeFirstComparison_yoneda (a : V → ℤ)
    (x : vertexTwistCellCohomology R V a 0) :
    vertexTwistNativeFirstComparison R V a x = -(vertexTwistCellActualLinearEquiv R V a 0 x) :=
  nativeCubicalFirstComparison_yoneda _ _ _ (vertexTwistCellSheaf_terms_acyclic R V a) x

/-- The independently specified native first roof is a linear equivalence for the original geometric base actions. -/
def vertexTwistNativeFirstLinearEquiv (a : V → ℤ) :
    letI := vertexTwistCellModule R V a 0
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) 1) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) 1
    vertexTwistCellCohomology R V a 0 ≃ₗ[R] Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) 1 := by
  letI := vertexTwistCellModule R V a 0
  letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) 1) :=
    schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) 1
  let e := AddEquiv.ofBijective (vertexTwistNativeFirstComparison R V a)
    (nativeCubicalFirstComparison_bijective _ _ _ (vertexTwistCellSheaf_terms_acyclic R V a))
  refine e.toLinearEquiv ?_
  intro r x
  change vertexTwistNativeFirstComparison R V a (r • x) = r • vertexTwistNativeFirstComparison R V a x
  rw [vertexTwistNativeFirstComparison_yoneda,vertexTwistNativeFirstComparison_yoneda,map_smul,smul_neg]

/-- The linear equivalence retains the independently specified native roof itself. -/
theorem vertexTwistNativeFirstLinearEquiv_apply (a : V → ℤ)
    (x : vertexTwistCellCohomology R V a 0) :
    vertexTwistNativeFirstLinearEquiv R V a x = vertexTwistNativeFirstComparison R V a x := rfl

end
end BPFixedPoints.ProjectiveLine
