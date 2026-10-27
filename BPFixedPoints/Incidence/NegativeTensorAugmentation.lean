import BPFixedPoints.Incidence.SingleCochainTensorMap
import BPFixedPoints.Incidence.ResolutionNativeAugmentation

/-! # Negative extension of a tensor augmentation is the tensor of the input augmentations

For two original nonnegative chain complexes with original augmentations,
any augmentation of their native tensor that restricts to the tensor of
the two augmentations on bidegree (0,0) is, after the specified negative
tensor isomorphism, the native integer cochain tensor of the two original
negative augmentations followed by the canonical single tensor map.
This is an equality of independently constructed cochain maps.
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
variable {T : Type} [TopologicalSpace T]
local instance negativeTensorAugmentationSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize

/-- The native extension term identification in degree zero, written with the integer index zero. -/
abbrev negativeZeroTermIso (X : ChainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℕ) :=
  X.extendXIso ComplexShape.embeddingDownNat (by rfl : ComplexShape.embeddingDownNat.f 0=0)

variable (P Q : ChainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℕ)

private theorem negativeTensorIso_hom_zero :
    (negativeZeroTermIso (HomologicalComplex.tensorObj P Q)).inv ≫ (negativeTensorIso P Q).hom.f 0 =
      negativeTensorDegreeHom P Q 0 :=
  negativeTensorIso_hom_component P Q 0

private theorem negativeTensorDegreeHom_zero :
    ιTensorObj P Q 0 0 0 rfl ≫ negativeTensorDegreeHom P Q 0 =
      ((negativeZeroTermIso P).inv ⊗ₘ (negativeZeroTermIso Q).inv) ≫
        ιTensorObj (negativeComplex P) (negativeComplex Q) 0 0 0 (by simp) :=
  negativeTensorDegreeHom_inclusion P Q 0 0 0 rfl

/-- The original negative augmentation keeps its original coefficient on the degree-zero term. -/
@[reassoc] theorem negativeAugmentation_zero_term
    (X : ChainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℕ)
    {A : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
    (π : X.X 0 ⟶ A) (z : X.d 1 0 ≫ π=0) :
    (negativeZeroTermIso X).inv ≫ (negativeAugmentation X π z).f 0 =
      π ≫ (singleObjXSelf (ComplexShape.up ℤ) 0 A).inv := by
  rw [negativeAugmentation_component,Iso.inv_hom_id_assoc]

variable {A B : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
variable (πP : P.X 0 ⟶ A) (zP : P.d 1 0 ≫ πP=0) (πQ : Q.X 0 ⟶ B) (zQ : Q.d 1 0 ≫ πQ=0)
variable (τ : (HomologicalComplex.tensorObj P Q).X 0 ⟶ A ⊗ B)
  (zτ : (HomologicalComplex.tensorObj P Q).d 1 0 ≫ τ=0)

/-- A tensor augmentation restricting to the tensor of the original augmentations is the tensor of their negative extensions. -/
theorem negativeAugmentation_tensor (hτ : ιTensorObj P Q 0 0 0 rfl ≫ τ=πP ⊗ₘ πQ) :
    negativeAugmentation (HomologicalComplex.tensorObj P Q) τ zτ =
      (negativeTensorIso P Q).hom ≫
        HomologicalComplex.tensorHom (negativeAugmentation P πP zP) (negativeAugmentation Q πQ zQ) ≫
          (singleCochainTensorIso A B 0 0 0 (by simp)).hom := by
  apply to_single_hom_ext
  apply (cancel_epi (negativeZeroTermIso (HomologicalComplex.tensorObj P Q)).inv).mp
  rw [negativeAugmentation_zero_term]
  simp only [comp_f]
  rw [← Category.assoc ((negativeZeroTermIso _).inv),negativeTensorIso_hom_zero]
  apply mapBifunctor.hom_ext
  intro p q h
  change p+q=0 at h
  obtain rfl : p=0 := by omega
  obtain rfl : q=0 := by omega
  rw [← Category.assoc,hτ,← Category.assoc,negativeTensorDegreeHom_zero,Category.assoc,
    nativeCochainTensorHom_inclusion_assoc,singleCochainTensorIso_hom,singleCochainTensorMap_same]
  simp only [tensorHom_comp_tensorHom_assoc,negativeAugmentation_zero_term_assoc,Category.id_comp]
  simp only [Iso.inv_hom_id,Category.comp_id]

end
end BPFixedPoints.SheafTools.BinaryCells
