import BPFixedPoints.Incidence.VertexProjectiveTwistZeroRouteAgreement
import BPFixedPoints.Incidence.VertexProjectiveTwistProductTransfer

/-! # The unit of the product is the constant global section

The unit of the product on actual cohomology of nonpositive twists, read
through the original H0 restriction route to actual global sections, is the
global section whose original chart coordinates are the per-vertex constant
one on both charts.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory TopologicalSpace CechProduct
open SheafTools.BinaryCells SchemeTools ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]
local instance vertexUnitSectionHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _
variable [IsNoetherianRing R]

/-- The unit is the actual global section with the per-vertex constant one as its original chart coordinates. -/
theorem vertexNegativeUnit_globalZeroChain :
    letI := vertexTwistH0BaseModule R V 0
    vertexTwistGlobalZeroChain R V _ (vertexTwistH0SectionsLinearEquiv R V 0 (vertexNegativeUnit R V)) =
      chainUnit R := by
  let _ := vertexTwistH0BaseModule R V 0
  let _ := vertexTwistCellAtModule R V (fun v => -((0 : V → ℕ) v : ℤ)) 0
  exact (vertexTwistGlobalZeroChain_cellActualZero R V 0 (vertexTwistCellStateInclusion R V 0 0
    ⟨cohomologyUnit R,cohomologyUnit_mem_stateDegreePiece R⟩)).trans (vertexNegativeUnit_coefficient R V)

/-- Under the public state equivalence the unit is the state unit. -/
theorem vertexTwistStateLinearEquiv_unit :
    letI := vertexTwistStateCohomologyModule R V 0 0
    (vertexTwistStateLinearEquiv R V 0 0 (vertexNegativeUnit R V)).val = cohomologyUnit R := by
  let _ := vertexTwistStateCohomologyModule R V 0 0
  rw [vertexTwistStateLinearEquiv_eq_actualStateAt,vertexNegativeUnit_state]

end
end BPFixedPoints.ProjectiveLine
