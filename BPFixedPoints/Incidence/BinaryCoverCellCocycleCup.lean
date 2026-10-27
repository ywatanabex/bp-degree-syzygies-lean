import BPFixedPoints.Incidence.BinaryCoverCellSheafCup
import BPFixedPoints.Incidence.FiniteCubicalActualCohomology
import BPFixedPoints.Incidence.AcyclicResolutionCohomologyDegree

/-! # The actual cell cup on the original cocycles and boundary representatives

Use the existing exact tower, original cycles, and original boundary maps.
The actual degree-zero case is retained, with no incoming boundary, and
all positive cases retain the specified original cup primitives.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open AbelianTensor ExtResolutionTools
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
variable (b : SectionPairing F G H)
local instance cocycleCupSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize

/-- The original exact tower retains the original cell differential. -/
theorem cubicalTower_differential (n : ℕ) :
    (cubicalTower U).differential n = (sheafComplex U).d (n+1) n :=
  complexTower_differential _ _ n

/-- Original tower cycles are closed under the original actual cell differential. -/
theorem cubicalCycle_closed (n : ℕ) (x : (cubicalTower U).cycles F n) :
    (sheafComplex U).d (n+1) n ≫ x.val = 0 := by
  have hx : (cubicalTower U).differential n ≫ x.val = 0 := x.property
  simpa only [cubicalTower_differential] using hx

/-- The original actual cup restricts to the existing original closed-cochain groups. -/
def cubicalCyclesCupAt (n i j : ℕ) :
    (cubicalTower U).cycles F i →+ (cubicalTower U).cycles G j →+ (cubicalTower U).cycles H n where
  toFun x :=
    { toFun := fun y => ⟨actualCellCupAt U b n i j x.val y.val,by
        change (cubicalTower U).differential n ≫ _ = 0
        rw [cubicalTower_differential]
        exact actualCellCupAt_closed U b n i j x.val y.val
          (cubicalCycle_closed U i x) (cubicalCycle_closed U j y)⟩
      map_zero' := Subtype.ext (actualCellCupAt_zero_right U b n i j x.val)
      map_add' := fun y z => Subtype.ext (actualCellCupAt_add_right U b n i j x.val y.val z.val) }
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    exact Subtype.ext (actualCellCupAt_zero_left U b n i j y.val)
  map_add' := by
    intro x z
    apply AddMonoidHom.ext
    intro y
    exact Subtype.ext (actualCellCupAt_add_left U b n i j x.val z.val y.val)

/-- Every existing cocycle retains its originally specified actual cup morphism. -/
theorem cubicalCyclesCupAt_val (n i j : ℕ)
    (x : (cubicalTower U).cycles F i) (y : (cubicalTower U).cycles G j) :
    (cubicalCyclesCupAt U b n i j x y).val = actualCellCupAt U b n i j x.val y.val := rfl

/-- A left boundary has exactly the original left cup primitive. -/
theorem cubicalCyclesCupAt_left_boundary (n i j : ℕ)
    (f : (sheafComplex U).X i ⟶ F) (y : (cubicalTower U).cycles G j) :
    cubicalCyclesCupAt U b (n+1) (i+1) j ((cubicalTower U).boundary F i f) y =
      (cubicalTower U).boundary H n (actualCellCupAt U b n i j f y.val) := by
  apply Subtype.ext
  change actualCellCupAt U b (n+1) (i+1) j ((cubicalTower U).differential i ≫ f) y.val =
    (cubicalTower U).differential n ≫ actualCellCupAt U b n i j f y.val
  rw [cubicalTower_differential,cubicalTower_differential]
  exact (actualCellCupAt_left_boundary U b n i j f y.val (cubicalCycle_closed U j y)).symm

/-- A right boundary has the original cup primitive with the inverse original Koszul unit. -/
theorem cubicalCyclesCupAt_right_boundary (n i j : ℕ)
    (x : (cubicalTower U).cycles F i) (g : (sheafComplex U).X j ⟶ G) :
    cubicalCyclesCupAt U b (n+1) i (j+1) x ((cubicalTower U).boundary G j g) =
      (cubicalTower U).boundary H n
        ((((-1 : ℤˣ)^i)⁻¹) • actualCellCupAt U b n i j x.val g) := by
  apply Subtype.ext
  change actualCellCupAt U b (n+1) i (j+1) x.val ((cubicalTower U).differential j ≫ g) =
    (cubicalTower U).differential n ≫ ((((-1 : ℤˣ)^i)⁻¹) • actualCellCupAt U b n i j x.val g)
  rw [cubicalTower_differential,cubicalTower_differential,Linear.comp_units_smul,
    actualCellCupAt_right_boundary U b n i j x.val g (cubicalCycle_closed U i x),inv_smul_smul]

/-- Every original left boundary has zero cup class, also in actual output degree zero. -/
theorem cubicalCyclesCupAt_class_left_boundary (n i j : ℕ)
    (f : (sheafComplex U).X i ⟶ F) (y : (cubicalTower U).cycles G j) :
    (cubicalTower U).classAt H n
      (cubicalCyclesCupAt U b n (i+1) j ((cubicalTower U).boundary F i f) y) = 0 := by
  cases n with
  | zero =>
    apply Subtype.ext
    exact actualCellCupAt_zero_degree U b 0 (i+1) j (by omega) _ _
  | succ n => rw [cubicalCyclesCupAt_left_boundary,ExactTower.classAt_boundary]

/-- Every original right boundary has zero cup class with its original sign, also at output degree zero. -/
theorem cubicalCyclesCupAt_class_right_boundary (n i j : ℕ)
    (x : (cubicalTower U).cycles F i) (g : (sheafComplex U).X j ⟶ G) :
    (cubicalTower U).classAt H n
      (cubicalCyclesCupAt U b n i (j+1) x ((cubicalTower U).boundary G j g)) = 0 := by
  cases n with
  | zero =>
    apply Subtype.ext
    exact actualCellCupAt_zero_degree U b 0 i (j+1) (by omega) _ _
  | succ n => rw [cubicalCyclesCupAt_right_boundary,ExactTower.classAt_boundary]

end
end BPFixedPoints.SheafTools.BinaryCells
