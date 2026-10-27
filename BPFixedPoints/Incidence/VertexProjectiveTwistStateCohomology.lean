import BPFixedPoints.Incidence.VertexProjectiveTwistCellStateCohomology
import BPFixedPoints.Incidence.VertexProjectiveTwistH0States

/-! # Actual multi-twist cohomology is the original state degree piece

The original actual cell resolution and the previously specified signed
native chain comparison connect actual sheaf Ext to the original full
contraction projection and inclusion, in every original degree.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct SheafTools.BinaryCells
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]
noncomputable local instance vertexStateCohomologyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _

/-- The original geometric base action on the original actual cohomology, before the state comparison. -/
@[instance_reducible] noncomputable def vertexTwistStateCohomologyModule (d : V → ℕ) (j : ℕ) :
    Module R ((vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H j) :=
  SchemeTools.schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V (fun v => -(d v : ℤ))) j

variable [IsNoetherianRing R]

/-- In every positive degree, actual sheaf cohomology is the original state degree piece through the specified original representatives. -/
noncomputable def vertexTwistPositiveStateLinearEquiv (d : V → ℕ) (n : ℕ) :
    letI := vertexTwistStateCohomologyModule R V d (n+1)
    (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H (n+1) ≃ₗ[R] stateDegreePiece R d (n+1) := by
  letI := vertexTwistStateCohomologyModule R V d (n+1)
  letI := vertexTwistCellModule R V (fun v => -(d v : ℤ)) n
  exact (vertexTwistCellActualLinearEquiv R V _ n).symm.trans (vertexTwistCellStateLinearEquiv R V d n)

/-- Each specified original cell representative retains exactly its original full state projection in actual cohomology. -/
theorem vertexTwistPositiveStateLinearEquiv_representative (d : V → ℕ) (n : ℕ)
    (x : vertexTwistCellCycles R V d (n+1)) :
    letI := vertexTwistStateCohomologyModule R V d (n+1)
    letI := vertexTwistCellModule R V (fun v => -(d v : ℤ)) n
    vertexTwistPositiveStateLinearEquiv R V d n
      (vertexTwistCellActualLinearEquiv R V _ n (QuotientAddGroup.mk x)) =
        vertexTwistCellCycleProjection R V d (n+1) x := by
  letI := vertexTwistStateCohomologyModule R V d (n+1)
  letI := vertexTwistCellModule R V (fun v => -(d v : ℤ)) n
  change vertexTwistCellStateLinearEquiv R V d n
    ((vertexTwistCellActualLinearEquiv R V _ n).symm
      (vertexTwistCellActualLinearEquiv R V _ n (QuotientAddGroup.mk x))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The actual inverse state class is the original full inclusion, passed through the specified original connecting comparison. -/
theorem vertexTwistPositiveStateLinearEquiv_inverse (d : V → ℕ) (n : ℕ) (s : stateDegreePiece R d (n+1)) :
    letI := vertexTwistStateCohomologyModule R V d (n+1)
    letI := vertexTwistCellModule R V (fun v => -(d v : ℤ)) n
    (vertexTwistPositiveStateLinearEquiv R V d n).symm s =
      vertexTwistCellActualLinearEquiv R V _ n
        (QuotientAddGroup.mk (vertexTwistCellStateInclusion R V d (n+1) s)) := by
  letI := vertexTwistStateCohomologyModule R V d (n+1)
  letI := vertexTwistCellModule R V (fun v => -(d v : ℤ)) n
  apply (vertexTwistPositiveStateLinearEquiv R V d n).injective
  rw [LinearEquiv.apply_symm_apply,vertexTwistPositiveStateLinearEquiv_representative,
    vertexTwistCellCycleProjection_inclusion]

/-- Actual cohomology of every nonpositive multi-twist is its original state piece in every degree.
The degree-zero case is the previously established original chart restriction comparison. -/
noncomputable def vertexTwistStateLinearEquiv (d : V → ℕ) (j : ℕ) :
    letI := vertexTwistStateCohomologyModule R V d j
    (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H j ≃ₗ[R] stateDegreePiece R d j := by
  cases j with
  | zero => exact vertexTwistH0StateLinearEquiv R V d
  | succ n => exact vertexTwistPositiveStateLinearEquiv R V d n

end BPFixedPoints.ProjectiveLine
