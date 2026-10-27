import BPFixedPoints.Incidence.BinaryCoverIntegerTensorAugmentation

/-! # The original terminal diagonal is the standard tensor unit

The original terminal free-open sheaf is identified with the actual tensor
unit by sending its original coefficient-one generator to the unit
coefficient: first the original generator-preserving component
identification, then the original unique component coefficient, then the
native unit of the monoidal integer sheafification. Under this
identification the original terminal diagonal is the inverse standard left
unitor. The comparison is reduced, by the native monoidal coherence of
sheafification, to Mathlib's original module left unitor.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Opposite CechCubicalCell
open HomologicalComplex ExtResolutionTools AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type}

/-- The unique original component coefficient as a linear identification with the integers. -/
def componentUnitLinearEquiv : Components ℤ V ≃ₗ[ℤ] ℤ :=
  Finsupp.uniqueLinearEquiv ℤ ℤ (fun _ : V => (0 : Fin 1))

/-- The original component generator has unit coefficient. -/
theorem componentUnitLinearEquiv_generator :
    componentUnitLinearEquiv (V := V) (Finsupp.single (fun _ => 0) 1) = 1 := by
  simp [componentUnitLinearEquiv,Finsupp.uniqueLinearEquiv]

/-- The original constant component presheaf is the native integer module presheaf unit. -/
def componentModuleUnitIso :
    componentModulePresheaf (T := T) (V := V) ≅ 𝟙_ ((Opens T)ᵒᵖ ⥤ ModuleCat.{0} ℤ) :=
  (Functor.const (Opens T)ᵒᵖ).mapIso (componentUnitLinearEquiv (V := V)).toModuleIso

variable [Fintype V] [DecidableEq V]

/-- The original terminal sheaf and the actual tensor unit, preserving the original coefficient-one generator. -/
def actualTerminalUnitIso :
    actualTerminalSheaf (T := T) ≅ 𝟙_ (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  actualComponentTopIso (T := T) (V := V) ≪≫
    integerSheafification.mapIso (componentModuleUnitIso (T := T) (V := V)) ≪≫
      (Functor.Monoidal.εIso (integerSheafification (T := T))).symm

omit [Fintype V] [DecidableEq V] in
/-- On constant module presheaves the original component diagonal is the inverse native left unitor. -/
private theorem componentDiagonal_unit :
    (Functor.const (Opens T)ᵒᵖ).map (componentTensorFold ℤ V).symm.toModuleIso.hom ≫
        (componentTensorPresheafIso (T := T) (V := V)).inv ≫
          ((componentModuleUnitIso (T := T) (V := V)).hom ⊗ₘ (componentModuleUnitIso (T := T) (V := V)).hom) =
      (componentModuleUnitIso (T := T) (V := V)).hom ≫ (λ_ (𝟙_ ((Opens T)ᵒᵖ ⥤ ModuleCat.{0} ℤ))).inv := by
  ext W x
  change TensorProduct.map (componentUnitLinearEquiv (V := V)).toLinearMap
      (componentUnitLinearEquiv (V := V)).toLinearMap ((componentTensorFold ℤ V).symm x) =
    (TensorProduct.lid ℤ ℤ).symm (componentUnitLinearEquiv (V := V) x)
  simp [componentTensorFold,componentUnitLinearEquiv,TensorProduct.congr_symm]

/-- The original terminal diagonal is the inverse standard left unitor of the actual tensor unit. -/
theorem actualTerminalDiagonal_unit :
    actualTerminalDiagonal (V := V) (T := T) ≫
        ((actualTerminalUnitIso (T := T) (V := V)).hom ⊗ₘ (actualTerminalUnitIso (T := T) (V := V)).hom) =
      (actualTerminalUnitIso (T := T) (V := V)).hom ≫
        (λ_ (𝟙_ (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}))).inv := by
  have ht : (actualTensorTerminalIso (V := V) (T := T)).hom =
      (presheafToSheaf _ AddCommGrpCat).map (terminalComponentDiagonal (V := V) (T := T)) ≫
        integerSheafification.map (componentTensorPresheafIso (T := T) (V := V)).inv ≫
          Functor.OplaxMonoidal.δ integerSheafification _ _ := by
    have hcti : (actualComponentTensorIso (T := T) (V := V)).inv =
        integerSheafification.map (componentTensorPresheafIso (T := T) (V := V)).inv ≫
          Functor.OplaxMonoidal.δ integerSheafification _ _ := by
      simp only [actualComponentTensorIso,Iso.trans_inv,Functor.mapIso_inv,Functor.Monoidal.μIso_inv]
    rw [← hcti,← actualTensorTerminalIso_component,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  have hl : (λ_ (integerSheafification.obj (𝟙_ ((Opens T)ᵒᵖ ⥤ ModuleCat.{0} ℤ)))).inv =
      integerSheafification.map (λ_ (𝟙_ ((Opens T)ᵒᵖ ⥤ ModuleCat.{0} ℤ))).inv ≫
        Functor.OplaxMonoidal.δ integerSheafification _ _ ≫
          (Functor.OplaxMonoidal.η (integerSheafification (T := T)) ▷ _) := by
    rw [Functor.Monoidal.map_leftUnitor_inv,Category.assoc,Category.assoc,Functor.Monoidal.μ_δ_assoc,
      ← comp_whiskerRight,Functor.Monoidal.ε_η,id_whiskerRight,Category.comp_id]
  simp only [actualTerminalDiagonal,actualTerminalUnitIso,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,
    Category.assoc,Functor.Monoidal.εIso_inv]
  rw [tensorHom_comp_tensorHom,Iso.inv_hom_id_assoc,← tensorHom_comp_tensorHom,
    leftUnitor_inv_naturality,hl,ht]
  simp only [Category.assoc]
  rw [Functor.OplaxMonoidal.δ_natural_assoc]
  have key : (presheafToSheaf _ AddCommGrpCat).map (terminalComponentDiagonal (V := V) (T := T)) ≫
      integerSheafification.map (componentTensorPresheafIso (T := T) (V := V)).inv ≫
        integerSheafification.map ((componentModuleUnitIso (T := T) (V := V)).hom ⊗ₘ
          (componentModuleUnitIso (T := T) (V := V)).hom) =
      (actualComponentTopIso (T := T) (V := V)).hom ≫
        integerSheafification.map (componentModuleUnitIso (T := T) (V := V)).hom ≫
          integerSheafification.map (λ_ (𝟙_ ((Opens T)ᵒᵖ ⥤ ModuleCat.{0} ℤ))).inv := by
    rw [← terminalComponentDiagonalIso_hom]
    change (presheafToSheaf _ AddCommGrpCat).map ((topComponentPresheafIso (V := V) (T := T)).hom ≫
        toAbelianPresheaf.map ((Functor.const (Opens T)ᵒᵖ).map (componentTensorFold ℤ V).symm.toModuleIso.hom)) ≫
      (presheafToSheaf _ AddCommGrpCat).map (toAbelianPresheaf.map (componentTensorPresheafIso (T := T) (V := V)).inv) ≫
        (presheafToSheaf _ AddCommGrpCat).map (toAbelianPresheaf.map ((componentModuleUnitIso (T := T) (V := V)).hom ⊗ₘ
          (componentModuleUnitIso (T := T) (V := V)).hom)) =
      (presheafToSheaf _ AddCommGrpCat).map (topComponentPresheafIso (V := V) (T := T)).hom ≫
        (presheafToSheaf _ AddCommGrpCat).map (toAbelianPresheaf.map (componentModuleUnitIso (T := T) (V := V)).hom) ≫
          (presheafToSheaf _ AddCommGrpCat).map (toAbelianPresheaf.map (λ_ (𝟙_ ((Opens T)ᵒᵖ ⥤ ModuleCat.{0} ℤ))).inv)
    simp only [← Functor.map_comp,Category.assoc]
    rw [componentDiagonal_unit]
  slice_lhs 1 3 => rw [key]
  simp only [Category.assoc]
  rw [MonoidalCategory.tensorHom_def]

local instance terminalUnitSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
variable (U : V → Fin 2 → Opens T)

/-- The original terminal augmentation followed by the identification of the terminal sheaf with the tensor unit. -/
abbrev actualUnitNegativeAugmentation :=
  actualCellNegativeAugmentation U ≫
    (CochainComplex.singleFunctor _ 0).map (actualTerminalUnitIso (T := T) (V := V)).hom

/-- The tensor of the two unit input augmentations is the terminal input tensor followed by the unit identification. -/
theorem actualUnitNegativeAugmentation_tensor :
    HomologicalComplex.tensorHom (actualUnitNegativeAugmentation U) (actualUnitNegativeAugmentation U) ≫
        (singleCochainTensorIso _ _ 0 0 0 (by simp)).hom =
      HomologicalComplex.tensorHom (actualCellNegativeAugmentation U) (actualCellNegativeAugmentation U) ≫
        (singleCochainTensorIso _ _ 0 0 0 (by simp)).hom ≫ (CochainComplex.singleFunctor _ 0).map
          ((actualTerminalUnitIso (T := T) (V := V)).hom ⊗ₘ (actualTerminalUnitIso (T := T) (V := V)).hom) := by
  rw [← nativeCochainTensorHom_comp_assoc,singleCochainTensorIso_hom,singleCochainTensorMap_tensorHom,
    Category.comp_id,singleCochainTensorMap_factor _ 0 0 0 (by simp),singleCochainTensorIso_hom]

local instance terminalUnitDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasDerivedCategory.standard _
variable (hcover : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k)

/-- The derived denominator given by the two original input augmentations into the actual tensor unit. -/
def actualUnitTensorAugmentationIso :=
  actualInputTensorAugmentationIso U hcover ≪≫ DerivedCategory.Q.mapIso
    ((CochainComplex.singleFunctor _ 0).mapIso
      (tensorIso (actualTerminalUnitIso (T := T) (V := V)) (actualTerminalUnitIso (T := T) (V := V))))

/-- This denominator is exactly the tensor of the two unit input augmentations and the canonical single map. -/
theorem actualUnitTensorAugmentationIso_hom :
    (actualUnitTensorAugmentationIso U hcover).hom =
      DerivedCategory.Q.map (HomologicalComplex.tensorHom (actualUnitNegativeAugmentation U)
        (actualUnitNegativeAugmentation U) ≫ (singleCochainTensorIso _ _ 0 0 0 (by simp)).hom) := by
  rw [actualUnitTensorAugmentationIso,Iso.trans_hom,actualInputTensorAugmentationIso_hom,Functor.mapIso_hom,
    Functor.mapIso_hom,tensorIso_hom,← Functor.map_comp,actualUnitNegativeAugmentation_tensor,Category.assoc]

variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (b : SectionPairing F G H)
variable (i j : ℕ) (x : (sheafComplex U).X i ⟶ F) (hx : (sheafComplex U).d (i+1) i ≫ x=0)
variable (y : (sheafComplex U).X j ⟶ G) (hy : (sheafComplex U).d (j+1) j ≫ y=0)

/-- The original cup roof: the identification with the tensor unit, the inverse standard left unitor, the inverse tensor of the two unit input augmentations, and the tensor of the original input maps. -/
theorem actualCellNativeRoof_unit_tensor :
    actualCellNativeRoof U hcover (i+j) (actualCellCupAt U b (i+j) i j x y)
      (actualCellCupAt_closed U b (i+j) i j x y hx hy) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
          ((actualTerminalUnitIso (T := T) (V := V)).hom ≫
            (λ_ (𝟙_ (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}))).inv)) ≫
        (actualUnitTensorAugmentationIso U hcover).inv ≫
          DerivedCategory.Q.map (nativeIntegerTensorCocycleMap U b i j x hx y hy) := by
  have hinv : (actualUnitTensorAugmentationIso U hcover).inv =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        ((actualTerminalUnitIso (T := T) (V := V)).inv ⊗ₘ (actualTerminalUnitIso (T := T) (V := V)).inv)) ≫
          (actualInputTensorAugmentationIso U hcover).inv := by
    simp only [actualUnitTensorAugmentationIso,Iso.trans_inv,Functor.mapIso_inv,tensorIso_inv]
  rw [actualCellNativeRoof_input_tensor U hcover b i j x hx y hy,← actualTerminalDiagonal_unit,hinv]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc,← Functor.map_comp]
  simp only [Category.assoc,tensorHom_comp_tensorHom,Iso.hom_inv_id,MonoidalCategory.id_tensorHom_id,
    Category.comp_id]
end
end BPFixedPoints.SheafTools.BinaryCells
