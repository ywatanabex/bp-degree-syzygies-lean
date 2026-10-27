import BPFixedPoints.Incidence.BinaryCoverCellActualTensorComplex

/-! # The actual standard tensor retains the original augmentation

The actual augmentation is defined independently by tensoring the two
original component augmentations and descending the native degree-zero
coproduct. The specified tensor comparison preserves that map and the
original terminal augmentation of the cubical diagonal.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open scoped BPFixedPoints.SheafTools.AbelianTensor TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance actualAugmentationSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize

/-- The original component presheaf, before forgetting or sheafification. -/
abbrev componentModulePresheaf : (Opens T)ᵒᵖ ⥤ ModuleCat.{0} ℤ :=
  (Functor.const (Opens T)ᵒᵖ).obj (ModuleCat.of ℤ (CechCubicalCell.Components ℤ V))

/-- The native tensor of constant component presheaves is the original constant tensor presheaf. -/
def componentTensorPresheafIso : componentModulePresheaf (T := T) (V := V) ⊗
    componentModulePresheaf (T := T) (V := V) ≅
      (Functor.const (Opens T)ᵒᵖ).obj
        (ModuleCat.of ℤ (CechCubicalCell.Components ℤ V ⊗[ℤ] CechCubicalCell.Components ℤ V)) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro W Z f; simp)

/-- The same original actual component sheaf, with no state-space action or identification. -/
abbrev actualComponentSheaf := integerSheafification.obj (componentModulePresheaf (T := T) (V := V))

/-- The original component augmentation after only its original forgetting and sheafification. -/
def actualComponentAugmentation : (sheafComplex U).X 0 ⟶ actualComponentSheaf (T := T) (V := V) :=
  integerSheafification.map (componentPresheafAugmentation U ℤ)

/-- The actual component tensor comparison uses only native tensor sheafification and constant presheaves. -/
def actualComponentTensorIso : actualComponentSheaf (T := T) (V := V) ⊗
    actualComponentSheaf (T := T) (V := V) ≅
      (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).obj
        (pairedComponentAbelianPresheaf (V := V) (T := T)) :=
  Functor.Monoidal.μIso integerSheafification _ _ ≪≫
    integerSheafification.mapIso (componentTensorPresheafIso (T := T) (V := V))

/-- The native actual tensor augmentation descends the original actual augmentations themselves. -/
def actualTensorAugmentation : (actualTensorSheafComplex U).X 0 ⟶
    actualComponentSheaf (T := T) (V := V) ⊗ actualComponentSheaf (T := T) (V := V) :=
  HomologicalComplex.mapBifunctorDesc (fun i j h => by
    change i+j=0 at h
    have hi : i=0 := by omega
    have hj : j=0 := by omega
    subst i; subst j
    exact actualComponentAugmentation U ⊗ₘ actualComponentAugmentation U)

/-- The old presheaf augmentation on its bidegree summand is the tensor of the original augmentations. -/
theorem tensorComponentPairMap_tensor : tensorComponentPairMap U ℤ =
    (componentPresheafAugmentation U ℤ ⊗ₘ componentPresheafAugmentation U ℤ) ≫
      (componentTensorPresheafIso (T := T) (V := V)).hom := by
  apply NatTrans.ext
  funext W
  change ModuleCat.ofHom _ = ModuleCat.ofHom _ ≫ 𝟙 _
  rw [Category.comp_id]
  rfl

/-- The actual standard comparison preserves the independently specified original tensor augmentation. -/
theorem actualTensorAugmentation_comparison :
    (actualTensorTermIso U 0).hom ≫ tensorSheafAugmentation U =
      actualTensorAugmentation U ≫ (actualComponentTensorIso (T := T) (V := V)).hom := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  change i+j=0 at h
  have hi : i=0 := by omega
  have hj : j=0 := by omega
  subst i; subst j
  rw [← Category.assoc,actualTensorInclusion_comparison]
  change (actualCellTensorIso U 0 0).hom ≫ integerSheafification.map (tensorPresheafInclusion ℤ U 0 0 0 h) ≫
    integerSheafification.map (tensorComponentPresheafAugmentation U ℤ) = _
  rw [← Functor.map_comp,tensorComponentPresheafAugmentation,
    HomologicalComplex.ι_mapBifunctorDesc]
  rw [← Category.assoc,actualTensorAugmentation,HomologicalComplex.ι_mapBifunctorDesc]
  change (actualCellTensorIso U 0 0).hom ≫ integerSheafification.map (tensorComponentPairMap U ℤ) =
    (actualComponentAugmentation U ⊗ₘ actualComponentAugmentation U) ≫
      (actualComponentTensorIso (T := T) (V := V)).hom
  rw [tensorComponentPairMap_tensor,Functor.map_comp]
  change (actualCellTensorIso U 0 0).hom ≫
    integerSheafification.map (componentPresheafAugmentation U ℤ ⊗ₘ componentPresheafAugmentation U ℤ) ≫
      integerSheafification.map (componentTensorPresheafIso (T := T) (V := V)).hom =
    (integerSheafification.map (componentPresheafAugmentation U ℤ) ⊗ₘ
      integerSheafification.map (componentPresheafAugmentation U ℤ)) ≫
        (Functor.Monoidal.μIso integerSheafification _ _).hom ≫
          integerSheafification.map (componentTensorPresheafIso (T := T) (V := V)).hom
  simp only [actualCellTensorIso,Functor.Monoidal.μIso_hom]
  rw [← Category.assoc,← Functor.LaxMonoidal.μ_natural,Category.assoc]

/-- The actual standard augmentation kills its actual degree-one total boundary. -/
theorem actualTensorAugmentation_zero :
    (actualTensorSheafComplex U).d 1 0 ≫ actualTensorAugmentation U = 0 := by
  apply (cancel_mono (actualComponentTensorIso (T := T) (V := V)).hom).1
  rw [Category.assoc,← actualTensorAugmentation_comparison,← Category.assoc,
    ← actualTensorTermIso_boundary U 0,Category.assoc,tensorSheafAugmentation_zero,comp_zero,zero_comp]

/-- The original diagonal into the actual tensor preserves the original terminal augmentation. -/
theorem actualTensorDiagonal_augmentation :
    (actualTensorDiagonalMap U).f 0 ≫ actualTensorAugmentation U ≫
      (actualComponentTensorIso (T := T) (V := V)).hom = augmentation U ≫
        (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).map
          (terminalComponentDiagonal (V := V) (T := T)) := by
  rw [← actualTensorAugmentation_comparison]
  change (tensorSheafDiagonalMap U).f 0 ≫ (actualTensorComplexIso U).inv.f 0 ≫
    (actualTensorTermIso U 0).hom ≫ tensorSheafAugmentation U = _
  change (tensorSheafDiagonalMap U).f 0 ≫ (actualTensorTermIso U 0).inv ≫
    (actualTensorTermIso U 0).hom ≫ tensorSheafAugmentation U = _
  rw [Iso.inv_hom_id_assoc,tensorSheafDiagonal_augmentation]

end
end BPFixedPoints.SheafTools.BinaryCells
