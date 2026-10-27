import BPFixedPoints.Incidence.BinaryCoverCellAcyclic
import BPFixedPoints.Incidence.VertexProjectiveTwistHigherCohomology

/-! # Original cubical cell terms are acyclic against every integral vertex twist

Each specified original rectangular face is affine. Actual quasicoherent
cohomology vanishing supplies the relative Ext acyclicity of the original
cell sheaf complex, with no twist sign or nonemptiness assumption.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000
variable (R : Type) [CommRing R] [IsNoetherianRing R]
variable (V : Type) [Fintype V] [DecidableEq V]
noncomputable local instance vertexCellHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The actual original cell sheaf resolution terms are acyclic against the actual integral multi-twist. -/
theorem vertexTwistCellSheaf_terms_acyclic (a : V → ℤ) :
    ExtResolutionTools.ComplexAcyclicAgainst
      (SheafTools.BinaryCells.sheafComplex (vertexCoordinateOpen R V))
      (vertexTwistAbelianSheaf R V a) := by
  apply SheafTools.BinaryCells.sheafComplex_acyclic
  intro n q k
  exact SheafTools.quasicoherent_affineOpen_local_cohomology_eq_zero (vertexScheme R V) _
    (vertexBinaryFaceOpen_isAffine R V q.val) (vertexTwistSheaf R V a) k

end BPFixedPoints.ProjectiveLine
