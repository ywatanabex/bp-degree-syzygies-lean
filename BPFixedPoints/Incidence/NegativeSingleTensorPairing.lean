import BPFixedPoints.Incidence.NegativeTensorNaturality

/-! # The original single pairing survives the native negative tensor comparison

This compares the original natural-chain pairing after negative extension
with the actual tensor of the original negative single complexes. It is an
equality of cochain maps and retains the original sheaf coefficient map.
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
local instance negativeSingleTensorSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}

/-- The native extended single identification retains both original single self-identifications. -/
@[reassoc] theorem negativeSingleIso_term (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (n : ℕ) :
    (negativeTermIso (actualSingleChain F n) n).inv ≫ (negativeSingleIso n F).hom.f (-(n : ℤ)) =
      (singleObjXSelf (ComplexShape.down ℕ) n F).hom ≫
        (singleObjXSelf (ComplexShape.up ℤ) (-(n : ℤ)) F).inv := by
  rw [negativeSingleIso,extendSingleIso_hom_f _ _ _ _ (by rfl)]
  simp [negativeTermIso,Category.assoc]

/-- The native cochain tensor retains the original two input maps on every bidegree. -/
@[reassoc] theorem nativeCochainTensorHom_inclusion
    {K L M N : CochainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℤ}
    (u : K ⟶ M) (v : L ⟶ N) (p q n : ℤ) (h : p+q=n) :
    ιTensorObj K L p q n h ≫ (HomologicalComplex.tensorHom u v).f n =
      (u.f p ⊗ₘ v.f q) ≫ ιTensorObj M N p q n h := by
  simpa only [curriedTensor_map_app,curriedTensor_obj_map,MonoidalCategory.tensorHom_def,Category.assoc] using
    (ι_mapBifunctorMap u v (curriedTensor _) (ComplexShape.up ℤ) p q n h)

/-- Native cochain tensor preserves composition of the original two input maps. -/
@[reassoc] theorem nativeCochainTensorHom_comp
    {K L M N P Q : CochainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℤ}
    (u : K ⟶ M) (v : L ⟶ N) (u' : M ⟶ P) (v' : N ⟶ Q) :
    HomologicalComplex.tensorHom u v ≫ HomologicalComplex.tensorHom u' v' =
      HomologicalComplex.tensorHom (u ≫ u') (v ≫ v') := by
  ext n : 1
  simp only [comp_f]
  apply mapBifunctor.hom_ext
  intro p q h
  rw [← Category.assoc,nativeCochainTensorHom_inclusion u v,Category.assoc,
    nativeCochainTensorHom_inclusion u' v',nativeCochainTensorHom_inclusion (u ≫ u') (v ≫ v')]
  simp only [comp_f,tensorHom_comp_tensorHom_assoc]

variable (b : SectionPairing F G H)

/-- Negative extension and native cochain tensor retain the original single pairing as the same entire cochain map. -/
theorem negativeSingleTensorPairing (i j : ℕ) :
    negativeMap (HomologicalComplex.tensorObj (actualSingleChain F i) (actualSingleChain G j))
        (singleTensorPairingMap b i j) ≫ (negativeSingleIso (i+j) H).hom =
      (negativeTensorIso (actualSingleChain F i) (actualSingleChain G j)).hom ≫
        HomologicalComplex.tensorHom (negativeSingleIso i F).hom (negativeSingleIso j G).hom ≫
          singleCochainTensorPairingMap b (-(i : ℤ)) (-(j : ℤ)) (-((i+j : ℕ) : ℤ)) := by
  apply to_single_hom_ext
  apply (cancel_epi (negativeTermIso
    (HomologicalComplex.tensorObj (actualSingleChain F i) (actualSingleChain G j)) (i+j)).inv).mp
  simp only [comp_f,Category.assoc]
  rw [negativeMap_term_assoc,negativeSingleIso_term]
  conv_rhs => rw [← Category.assoc,negativeTensorIso_hom_component]
  apply mapBifunctor.hom_ext
  intro p q h
  change p+q=i+j at h
  by_cases hp : p=i
  · subst p
    have hq : q=j := by omega
    subst q
    rw [negativeTensorDegreeHom_inclusion_assoc]
    rw [nativeCochainTensorHom_inclusion_assoc]
    rw [singleCochainTensorPairingMap_same]
    simp only [singleTensorPairingMap,closedChainMap_component,Category.assoc]
    rw [singleTensorPairingTerm_same_assoc]
    simp only [tensorHom_comp_tensorHom_assoc,negativeSingleIso_term,negativeSingleIso_term_assoc,
      Category.assoc,Iso.inv_hom_id_assoc,Iso.inv_hom_id,Category.comp_id]
  · have hz := (tensorRight ((actualSingleChain G j).X q)).map_isZero
      (isZero_single_obj_X (ComplexShape.down ℕ) i F p hp)
    exact hz.eq_of_src _ _

end
end BPFixedPoints.SheafTools.BinaryCells
