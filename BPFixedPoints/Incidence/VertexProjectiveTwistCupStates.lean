import BPFixedPoints.Incidence.VertexProjectiveTwistCupCoefficient
import BPFixedPoints.Incidence.VertexProjectiveTwistCohomologyCup
import BPFixedPoints.Incidence.VertexProjectiveTwistCellStateCohomology

/-! # The original geometric cup retains the original state contraction product

Descend the already specified geometric cup through the original quotients.
Its state coordinates use the same original contraction projections, in
all nonnegative degrees. No product is defined by transport from states.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct CechCubicalCell SheafTools.BinaryCells
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- The original actual cocycle cup, with only equality transport of its target twist sum. -/
def vertexTwistNegativeCellCyclesCup (d e : V → ℕ) (i j : ℕ)
    (x : vertexTwistCellCycles R V d i) (y : vertexTwistCellCycles R V e j) :
    vertexTwistCellCycles R V (d+e) (i+j) :=
  (cubicalTower (vertexCoordinateOpen R V)).mapCycles
    (eqToHom (congrArg (vertexTwistAbelianSheaf R V) (vertexTwistNegativeAdd V d e))) (i+j)
      (cubicalCyclesCupAt (vertexCoordinateOpen R V)
        (vertexTwistAbelianSectionPairing R V (fun v => -(d v : ℤ)) (fun v => -(e v : ℤ))) (i+j) i j x y)

/-- The original cocycle cup keeps its previously specified original geometric cochain. -/
theorem vertexTwistNegativeCellCyclesCup_val (d e : V → ℕ) (i j : ℕ)
    (x : vertexTwistCellCycles R V d i) (y : vertexTwistCellCycles R V e j) :
    (vertexTwistNegativeCellCyclesCup R V d e i j x y).val =
      vertexTwistNegativeCellCup R V d e i j x.val y.val := rfl

/-- The original contraction projection of the geometric cup is the existing state cup, on all cocycles and degrees. -/
theorem vertexTwistNegativeCellCyclesCup_projection (d e : V → ℕ) (i j : ℕ)
    (x : vertexTwistCellCycles R V d i) (y : vertexTwistCellCycles R V e j) :
    (vertexTwistCellCycleProjection R V (d+e) (i+j) (vertexTwistNegativeCellCyclesCup R V d e i j x y)).val =
      cohomologyCup R d e (vertexTwistCellCycleProjection R V d i x).val
        (vertexTwistCellCycleProjection R V e j y).val := by
  simp only [vertexTwistCellCycleProjection_val,vertexTwistNegativeCellCyclesCup_val,
    vertexTwistNegativeCellCup_coefficient]
  exact (cohomologyCup_chain_projection R d e
    (vertexTwistCellCycleCoefficient_closed R V d i x)
    (vertexTwistCellCycleCoefficient_closed R V e j y)).symm

/-- The original all-degree state projection uses original cycles at zero and the existing quotient comparison above zero. -/
def vertexTwistCellStateAt (d : V → ℕ) : (n : ℕ) →
    vertexTwistCellCohomologyAt R V (fun v => -(d v : ℤ)) n →+ stateDegreePiece R d n
  | 0 => vertexTwistCellCycleProjection R V d 0
  | n+1 => (vertexTwistCellStateAddEquiv R V d n).toAddMonoidHom

/-- Every original quotient class retains exactly the original state projection of its original representative. -/
theorem vertexTwistCellStateAt_class (d : V → ℕ) (n : ℕ) (x : vertexTwistCellCycles R V d n) :
    vertexTwistCellStateAt R V d n
      ((cubicalTower (vertexCoordinateOpen R V)).classAt _ n x) = vertexTwistCellCycleProjection R V d n x := by
  cases n <;> rfl

/-- The original descended geometric cup, with only equality transport of its target twist sum. -/
def vertexTwistNegativeCellCohomologyCup (d e : V → ℕ) (i j : ℕ) :
    vertexTwistCellCohomologyAt R V (fun v => -(d v : ℤ)) i →+
      vertexTwistCellCohomologyAt R V (fun v => -(e v : ℤ)) j →+
        vertexTwistCellCohomologyAt R V (fun v => -((d+e) v : ℤ)) (i+j) :=
  (vertexTwistCellCohomologyCupAt R V _ _ (i+j) i j).compr₂
    ((cubicalTower (vertexCoordinateOpen R V)).mapAt
      (eqToHom (congrArg (vertexTwistAbelianSheaf R V) (vertexTwistNegativeAdd V d e))) (i+j))

/-- The original descended cup still maps every original pair of classes to the class of their original geometric cup. -/
theorem vertexTwistNegativeCellCohomologyCup_class (d e : V → ℕ) (i j : ℕ)
    (x : vertexTwistCellCycles R V d i) (y : vertexTwistCellCycles R V e j) :
    vertexTwistNegativeCellCohomologyCup R V d e i j
      ((cubicalTower (vertexCoordinateOpen R V)).classAt _ i x)
      ((cubicalTower (vertexCoordinateOpen R V)).classAt _ j y) =
        (cubicalTower (vertexCoordinateOpen R V)).classAt _ (i+j)
          (vertexTwistNegativeCellCyclesCup R V d e i j x y) := by
  unfold vertexTwistNegativeCellCohomologyCup
  rw [AddMonoidHom.compr₂_apply,vertexTwistCellCohomologyCupAt_class,
    ExtResolutionTools.ExactTower.mapAt_class]
  rfl

/-- On every original cohomology class, the descended geometric cup preserves the original state product in all degrees. -/
theorem vertexTwistNegativeCellCohomologyCup_states (d e : V → ℕ) (i j : ℕ)
    (x : vertexTwistCellCohomologyAt R V (fun v => -(d v : ℤ)) i)
    (y : vertexTwistCellCohomologyAt R V (fun v => -(e v : ℤ)) j) :
    (vertexTwistCellStateAt R V (d+e) (i+j) (vertexTwistNegativeCellCohomologyCup R V d e i j x y)).val =
      cohomologyCup R d e (vertexTwistCellStateAt R V d i x).val (vertexTwistCellStateAt R V e j y).val := by
  obtain ⟨x,rfl⟩ := (cubicalTower (vertexCoordinateOpen R V)).classAt_surjective _ i x
  obtain ⟨y,rfl⟩ := (cubicalTower (vertexCoordinateOpen R V)).classAt_surjective _ j y
  rw [vertexTwistNegativeCellCohomologyCup_class,vertexTwistCellStateAt_class,
    vertexTwistCellStateAt_class,vertexTwistCellStateAt_class]
  exact vertexTwistNegativeCellCyclesCup_projection R V d e i j x y

end
end BPFixedPoints.ProjectiveLine
