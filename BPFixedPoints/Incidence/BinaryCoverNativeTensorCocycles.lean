import BPFixedPoints.Incidence.NativeSingleTensorPairing
import BPFixedPoints.Incidence.BinaryCoverActualTensorYoneda

/-! # The original tensor cocycle is the native tensor of its original single-degree maps -/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open TopologicalSpace Opposite ExtResolutionTools AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {T : Type} [TopologicalSpace T]
local instance tensorCocycleNativeSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize

private theorem nativeTensorHom_inclusion
    {P Q L M : ChainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℕ}
    (f : P ⟶ L) (g : Q ⟶ M) (p q n : ℕ) (h : p+q=n) :
    ιTensorObj P Q p q n h ≫ (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫ ιTensorObj L M p q n h := by
  simpa only [curriedTensor_map_app,curriedTensor_obj_map,MonoidalCategory.tensorHom_def,Category.assoc] using
    (ι_mapBifunctorMap f g (curriedTensor _) (ComplexShape.down ℕ) p q n h)

variable {V : Type} [Fintype V] [DecidableEq V] (U : V → Fin 2 → Opens T)
variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
variable (b : SectionPairing F G H)

/-- Tensor the original native closed-cochain maps and apply the independently specified native single-degree pairing. -/
def nativeTensorClosedMap (i j : ℕ) (x : (sheafComplex U).X i ⟶ F) (hx : (sheafComplex U).d (i+1) i ≫ x=0)
    (y : (sheafComplex U).X j ⟶ G) (hy : (sheafComplex U).d (j+1) j ≫ y=0) :
    actualTensorSheafComplex U ⟶ actualSingleChain H (i+j) :=
  HomologicalComplex.tensorHom
    (closedChainMap (sheafComplex U) i x hx)
    (closedChainMap (sheafComplex U) j y hy) ≫
      singleTensorPairingMap b i j

/-- The native tensor of representative maps equals the original independently specified actual tensor cocycle map. -/
theorem nativeTensorClosedMap_eq (i j : ℕ)
    (x : (sheafComplex U).X i ⟶ F) (hx : (sheafComplex U).d (i+1) i ≫ x=0)
    (y : (sheafComplex U).X j ⟶ G) (hy : (sheafComplex U).d (j+1) j ≫ y=0) :
    nativeTensorClosedMap U b i j x hx y hy =
      closedChainMap (actualTensorSheafComplex U) (i+j)
        (actualTensorCochain U b (i+j) i j x y)
        (by
          rw [actualTensorCochain_boundary,hx,hy]
          simp [actualTensorCochain,MonoidalPreadditive.zero_tensor,MonoidalPreadditive.tensor_zero]) := by
  apply to_single_hom_ext
  simp only [nativeTensorClosedMap,comp_f,singleTensorPairingMap,closedChainMap_component]
  apply mapBifunctor.hom_ext
  intro p q hpq
  change p+q=i+j at hpq
  rw [← Category.assoc,nativeTensorHom_inclusion]
  simp only [Category.assoc]
  by_cases hp : p=i
  · subst p
    by_cases hq : q=j
    · subst q
      rw [singleTensorPairingTerm_same_assoc]
      change _ = actualTensorInclusion U i j (i+j) hpq ≫
        actualTensorCochain U b (i+j) i j x y ≫ _
      rw [actualTensorCochain_inclusion_assoc]
      simp only [closedChainMap_component,← tensorHom_comp_tensorHom,Category.assoc,
        Iso.inv_hom_id,Category.comp_id,tensorHom_id]
      simp only [tensorHom_comp_tensorHom_assoc,Iso.inv_hom_id,tensorHom_id,id_whiskerRight,Category.id_comp]
    · rw [singleTensorPairingTerm_other_assoc b i j (i+j) i q hpq (Or.inr hq),zero_comp,comp_zero]
      change 0 = actualTensorInclusion U i q (i+j) hpq ≫
        actualTensorCochain U b (i+j) i j x y ≫ _
      rw [actualTensorCochain]
      simp only [← Category.assoc,actualTensorProjection_other U (i+j) i j i q hpq (Or.inr hq),zero_comp]
  · rw [singleTensorPairingTerm_other_assoc b i j (i+j) p q hpq (Or.inl hp),zero_comp,comp_zero]
    change 0 = actualTensorInclusion U p q (i+j) hpq ≫
      actualTensorCochain U b (i+j) i j x y ≫ _
    rw [actualTensorCochain]
    simp only [← Category.assoc,actualTensorProjection_other U (i+j) i j p q hpq (Or.inl hp),zero_comp]

end
end BPFixedPoints.SheafTools.BinaryCells
