import BPFixedPoints.Incidence.BinaryCoverActualTensorResolution
import BPFixedPoints.Incidence.BinaryCoverCellCocycleCup
import BPFixedPoints.Incidence.AcyclicResolutionAugmentedSourceNaturality

/-! # The specified actual tensor diagonal preserves original augmented Yoneda classes

Both sides use the original differential cokernels and augmentations.
The representative comparison needs no relative term acyclicity. This
identifies the specified resolution comparison; the canonical derived
external product of two Ext classes is a separate comparison.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Abelian TopologicalSpace Opposite
open ExtResolutionTools AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance tensorYonedaHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

/-- The exact tower of the existing actual standard tensor totalization, with its original cokernels. -/
abbrev actualTensorTower := complexTower (actualTensorSheafComplex U) (actualTensorSheafComplex_exact U)

/-- The specified original actual diagonal gives the specified original map of exact towers. -/
def actualTensorDiagonalSource : (cubicalTower U).SourceMap (actualTensorTower U) :=
  complexSourceMap (actualTensorDiagonalMap U) (sheafComplex_exact U) (actualTensorSheafComplex_exact U)

variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
variable (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)

/-- Every original tensor cocycle maps by its own original augmented iterated Yoneda class. -/
def actualTensorCocycleComparison (n : ℕ) (x : (actualTensorTower U).cycles F n) :
    Ext.{1} (actualComponentSheaf (T := T) (V := V) ⊗ actualComponentSheaf (T := T) (V := V)) F n := by
  letI := actualTensorAugmentation_epi U hcover
  exact augmentedComplexCocycleComparison _ F (actualTensorSheafComplex_exact U)
    (actualTensorAugmentation U) (actualTensorAugmentation_zero U) (actualTensorAugmentation_exact U) n x

/-- The original actual diagonal preserves the original augmented Yoneda representative in every degree. -/
theorem actualTensorDiagonal_cocycleComparison (n : ℕ) (x : (actualTensorTower U).cycles F n) :
    letI := augmentation_epi U hcover
    augmentedComplexCocycleComparison _ F (sheafComplex_exact U) (augmentation U)
      (augmentation_zero U) (augmentation_exact U) n ((actualTensorDiagonalSource U).cycles F n x) =
        (Ext.mk₀ (actualTensorTerminalIso (V := V) (T := T)).hom).comp
          (actualTensorCocycleComparison U F hcover n x) (zero_add n) := by
  letI := augmentation_epi U hcover
  letI := actualTensorAugmentation_epi U hcover
  exact augmentedComplexCocycleComparison_source F (sheafComplex_exact U) (augmentation U)
    (augmentation_zero U) (augmentation_exact U) (actualTensorDiagonalMap U)
    (actualTensorSheafComplex_exact U) (actualTensorAugmentation U) (actualTensorAugmentation_zero U)
    (actualTensorAugmentation_exact U) (actualTensorTerminalIso (V := V) (T := T)).hom
    (actualTensorDiagonal_augmentation_square U) n x

variable {F} {G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
variable (b : SectionPairing F G H)

/-- The original actual tensor of closed cochains is closed in the original exact tensor resolution. -/
def actualTensorCyclesCupAt (n i j : ℕ) (x : (cubicalTower U).cycles F i) (y : (cubicalTower U).cycles G j) :
    (actualTensorTower U).cycles H n :=
  ⟨actualTensorCochain U b n i j x.val y.val,by
    change (actualTensorTower U).differential n ≫ _=0
    rw [complexTower_differential,actualTensorCochain_boundary,
      cubicalCycle_closed U i x,cubicalCycle_closed U j y]
    simp [actualTensorCochain,MonoidalPreadditive.zero_tensor,MonoidalPreadditive.tensor_zero]⟩

/-- Pullback along the specified original diagonal gives exactly the existing original actual cup cocycle. -/
theorem actualTensorDiagonal_cyclesCupAt (n i j : ℕ)
    (x : (cubicalTower U).cycles F i) (y : (cubicalTower U).cycles G j) :
    (actualTensorDiagonalSource U).cycles H n (actualTensorCyclesCupAt U b n i j x y) =
      cubicalCyclesCupAt U b n i j x y := by
  apply Subtype.ext
  rfl

/-- The original actual cup retains the augmented Yoneda class of the original tensor cocycle and original diagonal. -/
theorem actualCellCupAt_tensorYoneda (n i j : ℕ)
    (x : (cubicalTower U).cycles F i) (y : (cubicalTower U).cycles G j) :
    letI := augmentation_epi U hcover
    augmentedComplexCocycleComparison _ H (sheafComplex_exact U) (augmentation U)
      (augmentation_zero U) (augmentation_exact U) n (cubicalCyclesCupAt U b n i j x y) =
        (Ext.mk₀ (actualTensorTerminalIso (V := V) (T := T)).hom).comp
          (actualTensorCocycleComparison U H hcover n (actualTensorCyclesCupAt U b n i j x y)) (zero_add n) := by
  rw [← actualTensorDiagonal_cyclesCupAt U b n i j x y]
  exact actualTensorDiagonal_cocycleComparison U H hcover n _

end
end BPFixedPoints.SheafTools.BinaryCells
