import BPFixedPoints.Incidence.VertexProjectiveTwistCupStates
import BPFixedPoints.Incidence.VertexProjectiveTwistStateCohomology

/-! # Specified actual Yoneda images of the original geometric cup retain state products

This is a representative comparison through the existing actual Ext
equivalence. Identification with canonical derived Ext cup remains separate.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct SheafTools.BinaryCells
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- Equality transport of degree retains the original state coordinate in the original full state module. -/
theorem vertexTwistCellStateAt_degree (d : V → ℕ) (m n : ℕ) (h : m=n)
    (x : vertexTwistCellCohomologyAt R V (fun v => -(d v : ℤ)) m) :
    (vertexTwistCellStateAt R V d n
      (Eq.mp (congrArg (vertexTwistCellCohomologyAt R V (fun v => -(d v : ℤ))) h) x)).val =
        (vertexTwistCellStateAt R V d m x).val := by
  subst n
  rfl

variable [IsNoetherianRing R]

/-- The original actual Ext image of every geometric cup class retains its specified original state product. -/
theorem vertexTwistNegativeCellCohomologyCup_actual_states (d e : V → ℕ)
    (i j n : ℕ) (h : i+j=n+1)
    (x : vertexTwistCellCohomologyAt R V (fun v => -(d v : ℤ)) i)
    (y : vertexTwistCellCohomologyAt R V (fun v => -(e v : ℤ)) j) :
    letI := vertexTwistStateCohomologyModule R V (d+e) (n+1)
    letI := vertexTwistCellModule R V (fun v => -((d+e) v : ℤ)) n
    (vertexTwistPositiveStateLinearEquiv R V (d+e) n
      (vertexTwistCellActualLinearEquiv R V _ n
        (Eq.mp (congrArg (vertexTwistCellCohomologyAt R V (fun v => -((d+e) v : ℤ))) h)
          (vertexTwistNegativeCellCohomologyCup R V d e i j x y)))).val =
      cohomologyCup R d e (vertexTwistCellStateAt R V d i x).val (vertexTwistCellStateAt R V e j y).val := by
  letI := vertexTwistStateCohomologyModule R V (d+e) (n+1)
  letI := vertexTwistCellModule R V (fun v => -((d+e) v : ℤ)) n
  change (vertexTwistCellStateLinearEquiv R V (d+e) n
    ((vertexTwistCellActualLinearEquiv R V _ n).symm (vertexTwistCellActualLinearEquiv R V _ n _))).val = _
  rw [LinearEquiv.symm_apply_apply]
  change (vertexTwistCellStateAt R V (d+e) (n+1)
    (Eq.mp (congrArg (vertexTwistCellCohomologyAt R V (fun v => -((d+e) v : ℤ))) h)
      (vertexTwistNegativeCellCohomologyCup R V d e i j x y))).val = _
  rw [vertexTwistCellStateAt_degree R V (d+e) (i+j) (n+1) h]
  exact vertexTwistNegativeCellCohomologyCup_states R V d e i j x y

end
end BPFixedPoints.ProjectiveLine
