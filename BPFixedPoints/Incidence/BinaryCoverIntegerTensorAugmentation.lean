import BPFixedPoints.Incidence.NegativeTensorAugmentation
import BPFixedPoints.Incidence.BinaryCoverIntegerTensorRoofs

/-! # The integer tensor denominator is the tensor of the two original input augmentations

The original independent tensor augmentation, transported through the
specified negative tensor isomorphism, equals the native integer cochain
tensor of the two original input augmentations followed by the canonical
degree-zero single tensor map. Both sides are constructed independently.
The original cup roof then has numerator and denominator given by the
tensor of the original input maps, after the original terminal diagonal.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open TopologicalSpace Opposite ExtResolutionTools AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance integerTensorAugmentationSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize

/-- The original terminal free-open sheaf, the target of the original cell augmentation. -/
abbrev actualTerminalSheaf : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0} :=
  (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).obj
    (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free)

/-- The original generator-preserving identification of the terminal sheaf with the actual component sheaf. -/
def actualComponentTopIso : actualTerminalSheaf (T := T) ≅ actualComponentSheaf (T := T) (V := V) :=
  (presheafToSheaf _ AddCommGrpCat).mapIso (topComponentPresheafIso (V := V) (T := T))

/-- The original component augmentation is the original terminal augmentation followed by this identification. -/
theorem augmentation_component :
    augmentation U ≫ (actualComponentTopIso (T := T) (V := V)).hom = actualComponentAugmentation U := by
  rw [augmentation,presheafAugmentation,actualComponentTopIso,Functor.mapIso_hom,← Functor.map_comp,
    Category.assoc,Iso.inv_hom_id,Category.comp_id]
  rfl

/-- The original component augmentation kills the original actual boundary. -/
theorem actualComponentAugmentation_zero : (sheafComplex U).d 1 0 ≫ actualComponentAugmentation U = 0 := by
  rw [← augmentation_component,← Category.assoc,augmentation_zero,zero_comp]

/-- On bidegree (0,0) the independent actual tensor augmentation is the tensor of the original component augmentations. -/
theorem actualTensorAugmentation_inclusion :
    ιTensorObj (sheafComplex U) (sheafComplex U) 0 0 0 rfl ≫ actualTensorAugmentation U =
      actualComponentAugmentation U ⊗ₘ actualComponentAugmentation U := by
  rw [actualTensorAugmentation,ι_mapBifunctorDesc]
  rfl

/-- The original terminal augmentation in native negative integer cochain degrees. -/
abbrev actualCellNegativeAugmentation :=
  negativeAugmentation (sheafComplex U) (augmentation U) (augmentation_zero U)

/-- The original component augmentation in native negative integer cochain degrees. -/
abbrev actualComponentNegativeAugmentation :=
  negativeAugmentation (sheafComplex U) (actualComponentAugmentation U) (actualComponentAugmentation_zero U)

/-- The two original input augmentations differ only by the original generator-preserving identification. -/
theorem actualComponentNegativeAugmentation_eq :
    actualComponentNegativeAugmentation U = actualCellNegativeAugmentation U ≫
      (CochainComplex.singleFunctor _ 0).map (actualComponentTopIso (T := T) (V := V)).hom := by
  have h := negativeAugmentation_source (augmentation U) (augmentation_zero U) (𝟙 _)
    (actualComponentAugmentation U) (actualComponentAugmentation_zero U)
    (actualComponentTopIso (T := T) (V := V)).hom (by rw [id_f,Category.id_comp,augmentation_component])
  rwa [negativeMap,extendMap_id,Category.id_comp] at h

/-- The independent tensor augmentation in negative degrees is the tensor of the two original component augmentations. -/
theorem actualTensorNegativeAugmentation_tensor :
    negativeAugmentation (actualTensorSheafComplex U) (actualTensorAugmentation U) (actualTensorAugmentation_zero U) =
      (negativeTensorIso (sheafComplex U) (sheafComplex U)).hom ≫
        HomologicalComplex.tensorHom (actualComponentNegativeAugmentation U) (actualComponentNegativeAugmentation U) ≫
          (singleCochainTensorIso _ _ 0 0 0 (by simp)).hom :=
  negativeAugmentation_tensor _ _ _ _ _ _ _ _ (actualTensorAugmentation_inclusion U)

/-- The same denominator through the two original terminal input augmentations and the component identification. -/
theorem actualTensorNegativeAugmentation_terminal :
    negativeAugmentation (actualTensorSheafComplex U) (actualTensorAugmentation U) (actualTensorAugmentation_zero U) =
      (negativeTensorIso (sheafComplex U) (sheafComplex U)).hom ≫
        HomologicalComplex.tensorHom (actualCellNegativeAugmentation U) (actualCellNegativeAugmentation U) ≫
          (singleCochainTensorIso _ _ 0 0 0 (by simp)).hom ≫ (CochainComplex.singleFunctor _ 0).map
            ((actualComponentTopIso (T := T) (V := V)).hom ⊗ₘ (actualComponentTopIso (T := T) (V := V)).hom) := by
  rw [actualTensorNegativeAugmentation_tensor,actualComponentNegativeAugmentation_eq,
    ← nativeCochainTensorHom_comp_assoc,singleCochainTensorIso_hom,singleCochainTensorMap_tensorHom,
    Category.comp_id,singleCochainTensorMap_factor _ 0 0 0 (by simp),singleCochainTensorIso_hom]

/-- The original terminal diagonal into the tensor square of the original terminal sheaf. -/
def actualTerminalDiagonal : actualTerminalSheaf (T := T) ⟶ actualTerminalSheaf (T := T) ⊗ actualTerminalSheaf (T := T) :=
  (actualTensorTerminalIso (V := V) (T := T)).hom ≫
    ((actualComponentTopIso (T := T) (V := V)).inv ⊗ₘ (actualComponentTopIso (T := T) (V := V)).inv)

local instance integerTensorAugmentationDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasDerivedCategory.standard _
variable (hcover : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k)

/-- The original independent integer tensor denominator is the tensor of the two original component augmentations. -/
theorem actualIntegerTensorAugmentationIso_hom :
    (actualIntegerTensorAugmentationIso U hcover).hom =
      DerivedCategory.Q.map (HomologicalComplex.tensorHom (actualComponentNegativeAugmentation U)
        (actualComponentNegativeAugmentation U) ≫ (singleCochainTensorIso _ _ 0 0 0 (by simp)).hom) := by
  change DerivedCategory.Q.map (negativeTensorIso (sheafComplex U) (sheafComplex U)).inv ≫
    DerivedCategory.Q.map (negativeAugmentation (actualTensorSheafComplex U) (actualTensorAugmentation U)
      (actualTensorAugmentation_zero U)) = _
  rw [actualTensorNegativeAugmentation_tensor,← Functor.map_comp,Iso.inv_hom_id_assoc]

/-- The derived denominator given by the two original terminal input augmentations. -/
def actualInputTensorAugmentationIso :=
  actualIntegerTensorAugmentationIso U hcover ≪≫ DerivedCategory.Q.mapIso
    ((CochainComplex.singleFunctor _ 0).mapIso
      (tensorIso (actualComponentTopIso (T := T) (V := V)) (actualComponentTopIso (T := T) (V := V)))).symm

/-- This denominator is exactly the tensor of the two original terminal input augmentations and the canonical single map. -/
theorem actualInputTensorAugmentationIso_hom :
    (actualInputTensorAugmentationIso U hcover).hom =
      DerivedCategory.Q.map (HomologicalComplex.tensorHom (actualCellNegativeAugmentation U)
        (actualCellNegativeAugmentation U) ≫ (singleCochainTensorIso _ _ 0 0 0 (by simp)).hom) := by
  change DerivedCategory.Q.map (negativeTensorIso (sheafComplex U) (sheafComplex U)).inv ≫
    DerivedCategory.Q.map (negativeAugmentation (actualTensorSheafComplex U) (actualTensorAugmentation U)
      (actualTensorAugmentation_zero U)) ≫ DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (tensorIso (actualComponentTopIso (T := T) (V := V)) (actualComponentTopIso (T := T) (V := V))).inv) = _
  rw [actualTensorNegativeAugmentation_terminal,← Functor.map_comp,← Functor.map_comp]
  congr 1
  simp only [Category.assoc,Iso.inv_hom_id_assoc,← Functor.map_comp,tensorIso_inv,tensorHom_comp_tensorHom,
    Iso.hom_inv_id,MonoidalCategory.id_tensorHom_id,CategoryTheory.Functor.map_id,Category.comp_id]

include hcover in
/-- The tensor of the two original terminal input augmentations is a native quasi-isomorphism. -/
theorem actualCellNegativeAugmentation_tensor_quasiIso :
    QuasiIso (HomologicalComplex.tensorHom (actualCellNegativeAugmentation U) (actualCellNegativeAugmentation U)) := by
  have := augmentation_epi U hcover
  have := actualTensorAugmentation_epi U hcover
  have := negativeAugmentation_quasiIso (actualTensorSheafComplex U) (actualTensorAugmentation U)
    (actualTensorAugmentation_zero U) (actualTensorSheafComplex_exact U) (actualTensorAugmentation_exact U)
  have h : HomologicalComplex.tensorHom (actualCellNegativeAugmentation U) (actualCellNegativeAugmentation U) =
      (negativeTensorIso (sheafComplex U) (sheafComplex U)).inv ≫
        negativeAugmentation (actualTensorSheafComplex U) (actualTensorAugmentation U)
          (actualTensorAugmentation_zero U) ≫ (CochainComplex.singleFunctor _ 0).map
            (tensorIso (actualComponentTopIso (T := T) (V := V)) (actualComponentTopIso (T := T) (V := V))).inv ≫
          (singleCochainTensorIso _ _ 0 0 0 (by simp)).inv := by
    rw [actualTensorNegativeAugmentation_terminal]
    simp only [Category.assoc,Iso.inv_hom_id_assoc,← Functor.map_comp_assoc,tensorIso_inv,
      tensorHom_comp_tensorHom,Iso.hom_inv_id,MonoidalCategory.id_tensorHom_id,
      CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id]
  rw [h]
  infer_instance

variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (b : SectionPairing F G H)
variable (i j : ℕ) (x : (sheafComplex U).X i ⟶ F) (hx : (sheafComplex U).d (i+1) i ≫ x=0)
variable (y : (sheafComplex U).X j ⟶ G) (hy : (sheafComplex U).d (j+1) j ≫ y=0)

/-- The input denominator followed by the component identification is the original integer tensor denominator. -/
theorem actualInputTensorAugmentationIso_component :
    (actualInputTensorAugmentationIso U hcover).hom ≫ DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        ((actualComponentTopIso (T := T) (V := V)).hom ⊗ₘ (actualComponentTopIso (T := T) (V := V)).hom)) =
      (actualIntegerTensorAugmentationIso U hcover).hom := by
  rw [actualInputTensorAugmentationIso,Iso.trans_hom,Functor.mapIso_hom,Iso.symm_hom,Functor.mapIso_inv,
    Category.assoc,← Functor.map_comp,← Functor.map_comp,tensorIso_inv,tensorHom_comp_tensorHom,
    Iso.inv_hom_id,MonoidalCategory.id_tensorHom_id,CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id,Category.comp_id]

/-- The integer tensor roof precomposed with the input denominator is the actual tensor numerator itself. -/
theorem actualIntegerTensorProductRoof_input :
    (actualInputTensorAugmentationIso U hcover).hom ≫ DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        ((actualComponentTopIso (T := T) (V := V)).hom ⊗ₘ (actualComponentTopIso (T := T) (V := V)).hom)) ≫
      actualIntegerTensorProductRoof U hcover b i j x hx y hy =
        DerivedCategory.Q.map (nativeIntegerTensorCocycleMap U b i j x hx y hy) := by
  rw [← Category.assoc,actualInputTensorAugmentationIso_component,actualIntegerTensorProductRoof,
    Iso.hom_inv_id_assoc]

/-- The original cup roof: the original terminal diagonal, the inverse tensor of the original input augmentations, and the tensor of the original input maps. -/
theorem actualCellNativeRoof_input_tensor :
    actualCellNativeRoof U hcover (i+j) (actualCellCupAt U b (i+j) i j x y)
      (actualCellCupAt_closed U b (i+j) i j x y hx hy) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map (actualTerminalDiagonal (V := V) (T := T))) ≫
        (actualInputTensorAugmentationIso U hcover).inv ≫
          DerivedCategory.Q.map (nativeIntegerTensorCocycleMap U b i j x hx y hy) := by
  rw [actualCellNativeRoof_integer_tensor U hcover b i j x hx y hy,
    ← actualIntegerTensorProductRoof_input U hcover b i j x hx y hy,Iso.inv_hom_id_assoc,
    actualTerminalDiagonal,← Functor.map_comp_assoc,← Functor.map_comp,Category.assoc,
    tensorHom_comp_tensorHom]
  simp only [Iso.inv_hom_id,MonoidalCategory.id_tensorHom_id,Category.comp_id]

end
end BPFixedPoints.SheafTools.BinaryCells
