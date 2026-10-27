import BPFixedPoints.Incidence.FiniteCubicalActualCohomology
import BPFixedPoints.Incidence.VertexProjectiveTwistCellAcyclic
import BPFixedPoints.Incidence.VertexProjectiveTwistTupleCech

/-! # Actual all-degree cubical cell cohomology for every integral vertex twist

The original polynomial binary charts, original cell boundary, actual
affine face vanishings and specified original terminal augmentation supply
the comparison with actual Ext-defined cohomology. The original geometric
base action is retained. Identification with the original state contraction
and preservation of products remain separate obligations.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory TopologicalSpace
open SheafTools.BinaryCells SchemeTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- The original cubical vertex chart is exactly the original polynomial chart. -/
theorem vertexCellChartOpen_eq (b : V → Fin 2) :
    chartOpen (vertexCoordinateOpen R V) b = vertexChartOpen R V b := by
  have hf (v : V) : SheafTools.binaryCoverFaceFactor (vertexCoordinateOpen R V v) (b v).castSucc =
      vertexCoordinateOpen R V v (b v) := by
    generalize b v = k
    fin_cases k <;> rfl
  simp only [chartOpen,vertexCell,SheafTools.binaryCoverFaceOpen,hf,vertexChartOpen_eq_coordinateOpen]

/-- The actual original cubical vertex charts cover the original product, including an empty vertex set. -/
theorem vertexCellChartOpen_cover :
    (⊤ : (vertexScheme R V).Opens) ≤ ⨆ b, chartOpen (vertexCoordinateOpen R V) b := by
  simp only [vertexCellChartOpen_eq]
  exact vertexChartOpen_iSup_top R V

noncomputable local instance vertexCellCohomologyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _

/-- Original cubical cell Hom cohomology in original degree `n+1`, modulo its original boundary image. -/
noncomputable abbrev vertexTwistCellCohomology (a : V → ℤ) (n : ℕ) :=
  cubicalCohomology (vertexCoordinateOpen R V) (vertexTwistAbelianSheaf R V a) n

/-- Original geometric scalar postcomposition acts on the original cubical cohomology before comparison. -/
@[instance_reducible] noncomputable def vertexTwistCellModule (a : V → ℤ) (n : ℕ) :
    Module R (vertexTwistCellCohomology R V a n) :=
  schemeBaseCubicalModule (vertexToBase R V) (vertexTwistSheaf R V a) (vertexCoordinateOpen R V) n

variable [IsNoetherianRing R]

/-- Every original integral multi-twist has its actual positive cohomology computed by the original bounded cubical cell complex,
linearly for the original geometric action and without supplied exactness or local vanishing hypotheses. -/
noncomputable def vertexTwistCellActualLinearEquiv (a : V → ℤ) (n : ℕ) :
    letI := vertexTwistCellModule R V a n
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) (n+1)) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) (n+1)
    vertexTwistCellCohomology R V a n ≃ₗ[R]
      Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) (n+1) :=
  schemeBaseFiniteCubicalActualLinearEquiv (vertexToBase R V) (vertexTwistSheaf R V a)
    (vertexCoordinateOpen R V) (vertexCellChartOpen_cover R V) (vertexTwistCellSheaf_terms_acyclic R V a) n

end BPFixedPoints.ProjectiveLine
