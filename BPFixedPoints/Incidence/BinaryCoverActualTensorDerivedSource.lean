import BPFixedPoints.Incidence.ResolutionNativeDerivedSource
import BPFixedPoints.Incidence.BinaryCoverActualTensorResolution

/-! # The original actual diagonal is the native derived lift of the original tensor unit map -/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex ExtResolutionTools
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance actualTensorNativeDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  HasDerivedCategory.standard _

/-- The original cell augmentation as its native derived-category denominator. -/
def actualCellNativeAugmentationIso (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b) := by
  letI := augmentation_epi U hcover
  exact nativeAugmentationIso (sheafComplex U) (augmentation U) (augmentation_zero U)
    (augmentation_exact U) (sheafComplex_exact U)

/-- The independent original tensor augmentation as its own native derived-category denominator. -/
def actualTensorNativeAugmentationIso (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b) := by
  letI := actualTensorAugmentation_epi U hcover
  exact nativeAugmentationIso (actualTensorSheafComplex U) (actualTensorAugmentation U)
    (actualTensorAugmentation_zero U) (actualTensorAugmentation_exact U) (actualTensorSheafComplex_exact U)

/-- The actual original diagonal in Mathlib's native derived category. -/
abbrev actualTensorNativeDerivedDiagonal := DerivedCategory.Q.map
  (negativeMap (sheafComplex U) (actualTensorDiagonalMap U))

/-- The original diagonal is precisely the canonical native derived lift through the original augmentations. -/
theorem actualTensorNativeDerivedDiagonal_formula (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b) :
    actualTensorNativeDerivedDiagonal U = (actualCellNativeAugmentationIso U hcover).hom ≫
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (actualTensorTerminalIso (V := V) (T := T)).hom) ≫
          (actualTensorNativeAugmentationIso U hcover).inv := by
  letI := augmentation_epi U hcover
  letI := actualTensorAugmentation_epi U hcover
  exact nativeDerivedMap_source (augmentation U) (augmentation_zero U) (augmentation_exact U)
    (sheafComplex_exact U) (actualTensorDiagonalMap U) (actualTensorAugmentation U)
    (actualTensorAugmentation_zero U) (actualTensorAugmentation_exact U) (actualTensorSheafComplex_exact U)
    (actualTensorTerminalIso (V := V) (T := T)).hom (actualTensorDiagonal_augmentation_square U)

/-- Any original actual chain lift of the same tensor unit map equals the specified diagonal in the derived category. -/
theorem actualTensorNativeDerivedDiagonal_unique (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
    (f : sheafComplex U ⟶ actualTensorSheafComplex U)
    (hf : f.f 0 ≫ actualTensorAugmentation U =
      augmentation U ≫ (actualTensorTerminalIso (V := V) (T := T)).hom) :
    DerivedCategory.Q.map (negativeMap (sheafComplex U) f)=actualTensorNativeDerivedDiagonal U := by
  letI := augmentation_epi U hcover
  letI := actualTensorAugmentation_epi U hcover
  exact nativeDerivedMap_unique (augmentation U) (augmentation_zero U) (augmentation_exact U)
    (sheafComplex_exact U) f (actualTensorAugmentation U) (actualTensorAugmentation_zero U)
    (actualTensorAugmentation_exact U) (actualTensorSheafComplex_exact U) (actualTensorDiagonalMap U)
    (actualTensorTerminalIso (V := V) (T := T)).hom hf (actualTensorDiagonal_augmentation_square U)

/-- The original actual diagonal is a native quasi-isomorphism, without relative term acyclicity. -/
theorem actualTensorDiagonal_quasiIso (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b) :
    QuasiIso (actualTensorDiagonalMap U) := by
  letI := augmentation_epi U hcover
  letI := actualTensorAugmentation_epi U hcover
  have h := negativeMap_quasiIso_of_augmentation_iso (augmentation U) (augmentation_zero U)
    (augmentation_exact U) (sheafComplex_exact U) (actualTensorDiagonalMap U)
    (actualTensorAugmentation U) (actualTensorAugmentation_zero U) (actualTensorAugmentation_exact U)
    (actualTensorSheafComplex_exact U) (actualTensorTerminalIso (V := V) (T := T)).hom
    (actualTensorDiagonal_augmentation_square U)
  exact (quasiIso_extendMap_iff (actualTensorDiagonalMap U) ComplexShape.embeddingDownNat).mp h

end
end BPFixedPoints.SheafTools.BinaryCells
