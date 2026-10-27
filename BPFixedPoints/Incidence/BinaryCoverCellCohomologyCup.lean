import BPFixedPoints.Incidence.BinaryCoverCellCocycleCup

/-! # The original actual cell cup descends through the original boundary quotients

Actual degree zero retains the original cycles. Every positive degree is
exactly the existing cubical cohomology quotient. Native quotient lifts
retain every original cup representative, without selecting a linear
right inverse or defining the product through state coordinates.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AbelianTensor ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
variable (b : SectionPairing F G H)

/-- The same existing cubical cohomology indexed by its actual cochain degree, with original cycles at zero. -/
abbrev cubicalCohomologyAt (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (n : ℕ) :=
  (cubicalTower U).cohomologyAt F n

/-- Every positive degree is exactly the original cubical quotient. -/
theorem cubicalCohomologyAt_succ (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (n : ℕ) :
    cubicalCohomologyAt U F (n+1) = cubicalCohomology U F n := rfl

/-- The original cocycle cup followed by its original cohomology class. -/
def cubicalCyclesCupClassAt (n i j : ℕ) :
    (cubicalTower U).cycles F i →+ (cubicalTower U).cycles G j →+ cubicalCohomologyAt U H n :=
  (cubicalCyclesCupAt U b n i j).compr₂ ((cubicalTower U).classAt H n)

/-- Descend the original right boundary quotient while retaining every original left cycle. -/
def cubicalCupRightLiftAt (n i j : ℕ) :
    (cubicalTower U).cycles F i →+ cubicalCohomologyAt U G j →+ cubicalCohomologyAt U H n where
  toFun x := (cubicalTower U).liftAt j (cubicalCyclesCupClassAt U b n i j x) (by
    cases j with
    | zero => trivial
    | succ j =>
      intro g
      exact cubicalCyclesCupAt_class_right_boundary U b n i j x g)
  map_zero' := by
    apply AddMonoidHom.ext
    intro y
    obtain ⟨y,rfl⟩ := (cubicalTower U).classAt_surjective G j y
    rw [ExactTower.liftAt_class]
    change cubicalCyclesCupClassAt U b n i j 0 y = 0
    rw [map_zero,AddMonoidHom.zero_apply]
  map_add' := by
    intro x z
    apply AddMonoidHom.ext
    intro y
    obtain ⟨y,rfl⟩ := (cubicalTower U).classAt_surjective G j y
    simp only [ExactTower.liftAt_class,map_add,AddMonoidHom.add_apply]

/-- Right quotient descent has the originally specified cup class on every representative. -/
theorem cubicalCupRightLiftAt_class (n i j : ℕ)
    (x : (cubicalTower U).cycles F i) (y : (cubicalTower U).cycles G j) :
    cubicalCupRightLiftAt U b n i j x ((cubicalTower U).classAt G j y) =
      (cubicalTower U).classAt H n (cubicalCyclesCupAt U b n i j x y) := by
  change (cubicalTower U).liftAt j (cubicalCyclesCupClassAt U b n i j x) _
    ((cubicalTower U).classAt G j y) = _
  rw [ExactTower.liftAt_class]
  rfl

/-- The actual cell cup on both original cohomology factors, including either degree-zero factor. -/
def cubicalCohomologyCupAt (n i j : ℕ) :
    cubicalCohomologyAt U F i →+ cubicalCohomologyAt U G j →+ cubicalCohomologyAt U H n :=
  (cubicalTower U).liftAt i (cubicalCupRightLiftAt U b n i j) (by
    cases i with
    | zero => trivial
    | succ i =>
      intro f
      apply AddMonoidHom.ext
      intro y
      obtain ⟨y,rfl⟩ := (cubicalTower U).classAt_surjective G j y
      rw [cubicalCupRightLiftAt_class]
      exact cubicalCyclesCupAt_class_left_boundary U b n i j f y)

/-- Both quotient lifts retain every originally specified cup representative, in all degrees. -/
theorem cubicalCohomologyCupAt_class (n i j : ℕ)
    (x : (cubicalTower U).cycles F i) (y : (cubicalTower U).cycles G j) :
    cubicalCohomologyCupAt U b n i j ((cubicalTower U).classAt F i x) ((cubicalTower U).classAt G j y) =
      (cubicalTower U).classAt H n (cubicalCyclesCupAt U b n i j x y) := by
  rw [cubicalCohomologyCupAt,ExactTower.liftAt_class,cubicalCupRightLiftAt_class]

/-- The homogeneous original cup lands in the sum of the original two cohomology degrees. -/
def cubicalCohomologyCup (i j : ℕ) :
    cubicalCohomologyAt U F i →+ cubicalCohomologyAt U G j →+ cubicalCohomologyAt U H (i+j) :=
  cubicalCohomologyCupAt U b (i+j) i j

/-- The actual cup introduces no quotient component outside its original sum degree. -/
theorem cubicalCohomologyCupAt_zero_degree (n i j : ℕ) (hne : i+j≠n)
    (x : cubicalCohomologyAt U F i) (y : cubicalCohomologyAt U G j) :
    cubicalCohomologyCupAt U b n i j x y = 0 := by
  obtain ⟨x,rfl⟩ := (cubicalTower U).classAt_surjective F i x
  obtain ⟨y,rfl⟩ := (cubicalTower U).classAt_surjective G j y
  rw [cubicalCohomologyCupAt_class]
  have he : cubicalCyclesCupAt U b n i j x y = 0 :=
    Subtype.ext (actualCellCupAt_zero_degree U b n i j hne x.val y.val)
  rw [he,map_zero]

end
end BPFixedPoints.SheafTools.BinaryCells
