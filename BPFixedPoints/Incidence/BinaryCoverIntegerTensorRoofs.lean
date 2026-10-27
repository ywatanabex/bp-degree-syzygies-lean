import BPFixedPoints.Incidence.NegativeTensorCocycleComparison
import BPFixedPoints.Incidence.BinaryCoverNativeCohomologyCup

/-! # Original cup roofs retain the actual integer cochain tensor of input maps

The specified cochain tensor isomorphism identifies the old independent
augmentation denominator with a denominator on the native integer tensor.
The numerator uses the actual tensor of the two original negative cochain
representatives. No cohomology product is transported from states.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.MonoidalCategory HomologicalComplex
open TopologicalSpace Opposite ExtResolutionTools AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance integerTensorRoofsDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasDerivedCategory.standard _
local instance integerTensorRoofsHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
variable (hcover : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k)

/-- The original independent augmentation denominator on the actual integer tensor, through the specified cochain isomorphism. -/
def actualIntegerTensorAugmentationIso :=
  (DerivedCategory.Q.mapIso (negativeTensorIso (sheafComplex U) (sheafComplex U))).symm ≪≫
    actualTensorNativeAugmentationIso U hcover

variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (b : SectionPairing F G H)
variable (i j : ℕ) (x : (sheafComplex U).X i ⟶ F) (hx : (sheafComplex U).d (i+1) i ≫ x=0)
variable (y : (sheafComplex U).X j ⟶ G) (hy : (sheafComplex U).d (j+1) j ≫ y=0)

/-- The native derived roof whose numerator tensors the actual integer cochain representatives themselves. -/
def actualIntegerTensorProductRoof :=
  (actualIntegerTensorAugmentationIso U hcover).inv ≫
    DerivedCategory.Q.map (nativeIntegerTensorCocycleMap U b i j x hx y hy)

/-- The original native tensor roof is exactly the actual integer cochain tensor roof through its original augmentation. -/
theorem actualNativeTensorProductRoof_integer :
    actualNativeTensorProductRoof U b hcover i j x hx y hy =
      actualIntegerTensorProductRoof U hcover b i j x hx y hy := by
  unfold actualNativeTensorProductRoof actualIntegerTensorProductRoof actualIntegerTensorAugmentationIso
  rw [← Functor.map_comp,negativeTensorClosedMap_native,Functor.map_comp]
  simp only [Iso.trans_inv,Iso.symm_inv,Functor.mapIso_hom,Category.assoc]

/-- Every original cup roof retains the actual integer tensor of its two native representatives, through the original tensor unit lift. -/
theorem actualCellNativeRoof_integer_tensor :
    actualCellNativeRoof U hcover (i+j) (actualCellCupAt U b (i+j) i j x y)
      (actualCellCupAt_closed U b (i+j) i j x y hx hy) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (actualTensorTerminalIso (V := V) (T := T)).hom) ≫
          actualIntegerTensorProductRoof U hcover b i j x hx y hy := by
  rw [actualCellNativeRoof_cup,actualNativeTensorProductRoof_integer]

/-- The original quotient cup has its actual native cohomology image computed by the actual integer cochain tensor of both original input maps. -/
theorem nativeCubicalComparison_cup_integer_tensor
    (u : (cubicalTower U).cycles F i) (v : (cubicalTower U).cycles G j) :
    nativeCubicalComparison U H hcover (i+j)
      (cubicalCohomologyCupAt U b (i+j) i j
        ((cubicalTower U).classAt F i u) ((cubicalTower U).classAt G j v)) =
      localSheafTopEquiv H (i+j) (Ext.homEquiv.symm
        ((DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
            (actualTensorTerminalIso (V := V) (T := T)).hom) ≫
          actualIntegerTensorProductRoof U hcover b i j u.val (cubicalCycle_closed U i u)
            v.val (cubicalCycle_closed U j v)) ≫
          ((DerivedCategory.singleFunctors _).shiftIso ((i+j : ℕ) : ℤ) (-((i+j : ℕ) : ℤ)) 0
            (by omega)).inv.app H)) := by
  rw [nativeCubicalComparison_cup_representative,actualNativeTensorProductRoof_integer]

end
end BPFixedPoints.SheafTools.BinaryCells
