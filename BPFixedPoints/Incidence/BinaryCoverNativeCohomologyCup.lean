import BPFixedPoints.Incidence.BinaryCoverNativeCohomology
import BPFixedPoints.Incidence.ResolutionNativeCupSign

/-! # The actual native cohomology image of the original quotient cup

This retains the actual derived tensor roof of the original input maps.
It does not define a product by transporting a state multiplication.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open ExtResolutionTools AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance nativeCohomologyCupHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance nativeCohomologyCupDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasDerivedCategory.standard _
variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
variable (b : SectionPairing F G H) (hcover : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k)

/-- Every original quotient cup representative has actual native cohomology image given by the native tensor roof of its original two input maps. -/
theorem nativeCubicalComparison_cup_representative (i j : ℕ)
    (x : (cubicalTower U).cycles F i) (y : (cubicalTower U).cycles G j) :
    nativeCubicalComparison U H hcover (i+j)
      (cubicalCohomologyCupAt U b (i+j) i j
        ((cubicalTower U).classAt F i x) ((cubicalTower U).classAt G j y)) =
      localSheafTopEquiv H (i+j) (Ext.homEquiv.symm
        ((DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
            (actualTensorTerminalIso (V := V) (T := T)).hom) ≫
          actualNativeTensorProductRoof U b hcover i j x.val (cubicalCycle_closed U i x)
            y.val (cubicalCycle_closed U j y)) ≫
          ((DerivedCategory.singleFunctors _).shiftIso ((i+j : ℕ) : ℤ) (-((i+j : ℕ) : ℤ)) 0
            (by omega)).inv.app H)) := by
  rw [cubicalCohomologyCupAt_class,nativeCubicalComparison_representative]
  exact congrArg (fun f => localSheafTopEquiv H (i+j) (Ext.homEquiv.symm
    (f ≫ ((DerivedCategory.singleFunctors _).shiftIso ((i+j : ℕ) : ℤ) (-((i+j : ℕ) : ℤ)) 0
      (by omega)).inv.app H)))
    (actualCellNativeRoof_cup U b hcover i j x.val (cubicalCycle_closed U i x)
      y.val (cubicalCycle_closed U j y))

end
end BPFixedPoints.SheafTools.BinaryCells
