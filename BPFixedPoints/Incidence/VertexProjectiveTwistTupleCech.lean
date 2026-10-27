import BPFixedPoints.Incidence.FiniteCechActualCohomology
import BPFixedPoints.Incidence.VertexProjectiveTwistCechAcyclic

/-! # Actual all-degree tuple Čech comparison for every original multi-twist

The original polynomial charts form the actual cover, and their actual affine
intersections supply every local vanishing. The twist is any integer-valued
function on an arbitrary finite vertex set. The source is the ordinary tuple
Čech Hom complex; its comparison with the finite cubical coefficient complex
is a separate remaining obligation.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
open SheafTools.FreeCech SchemeTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
variable (R : Type) [CommRing R] (V : Type) [Fintype V]

noncomputable local instance vertexTupleCechHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Original tuple Čech cohomology in degree `n+1`, retaining all repeated chart indices. -/
noncomputable abbrev vertexTwistTupleCechCohomology (a : V → ℤ) (n : ℕ) :=
  cechCohomology (vertexChartOpen R V) (vertexTwistAbelianSheaf R V a) n

/-- Coefficients act through the original structural morphism on the original tuple sections. -/
@[instance_reducible] noncomputable def vertexTwistTupleCechModule (a : V → ℤ) (n : ℕ) :
    Module R (vertexTwistTupleCechCohomology R V a n) :=
  schemeBaseFiniteCechModule (vertexToBase R V) (vertexTwistSheaf R V a) (vertexChartOpen R V) n

variable [IsNoetherianRing R]

/-- The actual native free-open resolution terms are acyclic for every original integer multi-twist. -/
theorem vertexTwistTupleCech_terms_acyclic (a : V → ℤ) :
    ExtResolutionTools.ComplexAcyclicAgainst
      (freeSheafComplex (Opens.grothendieckTopology (vertexScheme R V))
        (coverVertices (vertexChartOpen R V))) (vertexTwistAbelianSheaf R V a) := by
  classical
  exact freeSheafComplex_acyclic (vertexChartOpen R V) (vertexTwistAbelianSheaf R V a)
    (fun _ t k x => vertexTwistSheaf_chartIntersection_cohomology_eq_zero R V a t k x)

/-- In every positive degree the original tuple Čech cohomology is genuine Ext-defined cohomology,
linearly for the original geometric base action and without supplied local-vanishing hypotheses. -/
noncomputable def vertexTwistTupleCechActualLinearEquiv (a : V → ℤ) (n : ℕ) :
    letI := vertexTwistTupleCechModule R V a n
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) (n+1)) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) (n+1)
    vertexTwistTupleCechCohomology R V a n ≃ₗ[R]
      Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) (n+1) := by
  classical
  exact schemeBaseFiniteCechActualLinearEquiv (vertexToBase R V) (vertexTwistSheaf R V a)
    (vertexChartOpen R V) (vertexChartOpen_iSup_top R V)
    (fun _ t k x => vertexTwistSheaf_chartIntersection_cohomology_eq_zero R V a t k x) n

end BPFixedPoints.ProjectiveLine
