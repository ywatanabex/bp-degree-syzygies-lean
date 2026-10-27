import BPFixedPoints.Incidence.BinaryCoverActualTensorDerivedSource
import BPFixedPoints.Incidence.BinaryCoverNativeTensorCocycles
import BPFixedPoints.Incidence.ResolutionNativeRoofs

/-! # The original cup is the native tensor-product roof through the original unit lift

These are actual morphisms in Mathlib's derived category. No cup is
transported from states. Identification of these roofs with the earlier
iterated Yoneda representative in positive degree is a separate step.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open TopologicalSpace Opposite ExtResolutionTools AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance nativeCupRoofsDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasDerivedCategory.standard _

/-- The original cell cochain in the native derived category with its own original augmentation denominator. -/
def actualCellNativeRoof (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
    {H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (n : ℕ)
    (x : (sheafComplex U).X n ⟶ H) (hx : (sheafComplex U).d (n+1) n ≫ x=0) := by
  letI := augmentation_epi U hcover
  exact nativeCocycleRoof (sheafComplex U) (augmentation U) (augmentation_zero U)
    (augmentation_exact U) (sheafComplex_exact U) n x hx

/-- The original tensor cochain in the native derived category with its independent original tensor augmentation. -/
def actualTensorNativeRoof (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
    {H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (n : ℕ)
    (x : (actualTensorSheafComplex U).X n ⟶ H) (hx : (actualTensorSheafComplex U).d (n+1) n ≫ x=0) := by
  letI := actualTensorAugmentation_epi U hcover
  exact nativeCocycleRoof (actualTensorSheafComplex U) (actualTensorAugmentation U)
    (actualTensorAugmentation_zero U) (actualTensorAugmentation_exact U) (actualTensorSheafComplex_exact U) n x hx

/-- The original diagonal pulls the native tensor roof back through the original native tensor unit map. -/
theorem actualCellNativeRoof_diagonal (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
    {H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (n : ℕ)
    (x : (actualTensorSheafComplex U).X n ⟶ H) (hx : (actualTensorSheafComplex U).d (n+1) n ≫ x=0)
    (hfx : (sheafComplex U).d (n+1) n ≫ ((actualTensorDiagonalMap U).f n ≫ x)=0) :
    actualCellNativeRoof U hcover n ((actualTensorDiagonalMap U).f n ≫ x) hfx =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (actualTensorTerminalIso (V := V) (T := T)).hom) ≫ actualTensorNativeRoof U hcover n x hx := by
  letI := augmentation_epi U hcover
  letI := actualTensorAugmentation_epi U hcover
  exact nativeCocycleRoof_source (augmentation U) (augmentation_zero U) (augmentation_exact U)
    (sheafComplex_exact U) (actualTensorDiagonalMap U) (actualTensorAugmentation U)
    (actualTensorAugmentation_zero U) (actualTensorAugmentation_exact U) (actualTensorSheafComplex_exact U)
    (actualTensorTerminalIso (V := V) (T := T)).hom (actualTensorDiagonal_augmentation_square U) n x hx hfx

variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (b : SectionPairing F G H)
variable (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
variable (i j : ℕ) (x : (sheafComplex U).X i ⟶ F) (hx : (sheafComplex U).d (i+1) i ≫ x=0)
variable (y : (sheafComplex U).X j ⟶ G) (hy : (sheafComplex U).d (j+1) j ≫ y=0)

include hx hy in
private theorem tensorCochainClosed : (actualTensorSheafComplex U).d (i+j+1) (i+j) ≫
    actualTensorCochain U b (i+j) i j x y=0 := by
  rw [actualTensorCochain_boundary,hx,hy]
  simp [actualTensorCochain,MonoidalPreadditive.zero_tensor,MonoidalPreadditive.tensor_zero]

/-- The native roof obtained by tensoring the two native representative maps themselves. -/
def actualNativeTensorProductRoof :=
  (actualTensorNativeAugmentationIso U hcover).inv ≫
    DerivedCategory.Q.map (negativeMap (actualTensorSheafComplex U) (nativeTensorClosedMap U b i j x hx y hy)) ≫
      DerivedCategory.Q.map (negativeSingleIso (i+j) H).hom

/-- The old actual tensor cochain gives precisely the independently specified native tensor-product roof. -/
theorem actualTensorNativeRoof_product :
    actualTensorNativeRoof U hcover (i+j) (actualTensorCochain U b (i+j) i j x y)
      (tensorCochainClosed U b i j x hx y hy) = actualNativeTensorProductRoof U b hcover i j x hx y hy := by
  letI := actualTensorAugmentation_epi U hcover
  unfold actualNativeTensorProductRoof
  rw [nativeTensorClosedMap_eq]
  change (actualTensorNativeAugmentationIso U hcover).inv ≫
    DerivedCategory.Q.map (negativeCocycleMap (actualTensorSheafComplex U) (i+j)
      (actualTensorCochain U b (i+j) i j x y) _) = _
  rw [negativeCocycleMap,Functor.map_comp]

/-- The original actual cup has the native tensor-product roof through the original derived tensor-unit lift. -/
theorem actualCellNativeRoof_cup :
    actualCellNativeRoof U hcover (i+j) (actualCellCupAt U b (i+j) i j x y)
      (actualCellCupAt_closed U b (i+j) i j x y hx hy) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (actualTensorTerminalIso (V := V) (T := T)).hom) ≫
          actualNativeTensorProductRoof U b hcover i j x hx y hy := by
  rw [← actualTensorNativeRoof_product U b hcover i j x hx y hy]
  exact actualCellNativeRoof_diagonal U hcover (i+j) _
    (tensorCochainClosed U b i j x hx y hy) (actualCellCupAt_closed U b (i+j) i j x y hx hy)

end
end BPFixedPoints.SheafTools.BinaryCells
