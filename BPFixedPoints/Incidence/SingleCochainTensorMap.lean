import BPFixedPoints.Incidence.NativeCochainSingleTensorPairing
import BPFixedPoints.Incidence.NegativeSingleTensorPairing

/-! # The canonical single tensor map of native integer single complexes

An actual sheaf morphism on the native tensor of two single integer cochain
complexes, evaluated on the specified bidegree only. With the identity
morphism this is the canonical single tensor map, and it is an actual
cochain isomorphism. The original section pairings are its special case.
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
local instance singleCochainTensorMapSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
variable {F G H K : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}

/-- An actual sheaf morphism on the specified native integer single bidegree, and zero elsewhere. -/
def singleCochainTensorTerm (m : F ⊗ G ⟶ H) (p q n : ℤ) :
    (HomologicalComplex.tensorObj (actualSingleCochain F p) (actualSingleCochain G q)).X n ⟶ H :=
  mapBifunctorDesc (fun i j _ => by
    by_cases hi : i=p
    · subst i
      by_cases hj : j=q
      · subst j
        exact ((singleObjXSelf (ComplexShape.up ℤ) p F).hom ⊗ₘ
          (singleObjXSelf (ComplexShape.up ℤ) q G).hom) ≫ m
      · exact 0
    · exact 0)

/-- The specified bidegree retains the actual sheaf morphism. -/
@[reassoc] theorem singleCochainTensorTerm_same (m : F ⊗ G ⟶ H) (p q n : ℤ) (h : p+q=n) :
    ιTensorObj (actualSingleCochain F p) (actualSingleCochain G q) p q n h ≫
      singleCochainTensorTerm m p q n =
        ((singleObjXSelf (ComplexShape.up ℤ) p F).hom ⊗ₘ
          (singleObjXSelf (ComplexShape.up ℤ) q G).hom) ≫ m := by
  rw [singleCochainTensorTerm,ι_mapBifunctorDesc]
  simp only [dite_true]

/-- The single tensor map from an actual sheaf morphism, as a native cochain map. -/
def singleCochainTensorMap (m : F ⊗ G ⟶ H) (p q n : ℤ) :
    HomologicalComplex.tensorObj (actualSingleCochain F p) (actualSingleCochain G q) ⟶
      actualSingleCochain H n :=
  mkHomToSingle (singleCochainTensorTerm m p q n) (by
    intro k hk
    rw [singleCochainTensor_d_zero,zero_comp])

/-- The native cochain map retains the actual sheaf morphism on its specified bidegree. -/
@[reassoc] theorem singleCochainTensorMap_same (m : F ⊗ G ⟶ H) (p q n : ℤ) (h : p+q=n) :
    ιTensorObj (actualSingleCochain F p) (actualSingleCochain G q) p q n h ≫
      (singleCochainTensorMap m p q n).f n =
        ((singleObjXSelf (ComplexShape.up ℤ) p F).hom ⊗ₘ
          (singleObjXSelf (ComplexShape.up ℤ) q G).hom) ≫ m ≫
            (singleObjXSelf (ComplexShape.up ℤ) n H).inv := by
  rw [singleCochainTensorMap,mkHomToSingle_f,← Category.assoc,singleCochainTensorTerm_same,
    Category.assoc]

/-- Every other bidegree of the native single tensor has a zero source. -/
theorem singleCochainTensor_isZero_other (p q i j : ℤ) (hne : i≠p ∨ j≠q) :
    IsZero ((actualSingleCochain F p).X i ⊗ (actualSingleCochain G q).X j) := by
  rcases hne with hi | hj
  · exact (tensorRight ((actualSingleCochain G q).X j)).map_isZero
      (isZero_single_obj_X (ComplexShape.up ℤ) p F i hi)
  · exact (tensorLeft ((actualSingleCochain F p).X i)).map_isZero
      (isZero_single_obj_X (ComplexShape.up ℤ) q G j hj)

/-- The original section pairing map is the single tensor map of its own actual sheaf morphism. -/
theorem singleCochainTensorPairingMap_eq (b : SectionPairing F G H) (p q n : ℤ) :
    singleCochainTensorPairingMap b p q n = singleCochainTensorMap b.sheafMap p q n := by
  apply to_single_hom_ext
  apply mapBifunctor.hom_ext
  intro i j h
  change i+j=n at h
  by_cases hij : i=p ∧ j=q
  · obtain ⟨rfl,rfl⟩ := hij
    rw [singleCochainTensorPairingMap_same,singleCochainTensorMap_same]
  · exact (singleCochainTensor_isZero_other p q i j (by tauto)).eq_of_src _ _

/-- Postcomposition by an actual sheaf morphism is retained by the single tensor map. -/
theorem singleCochainTensorMap_comp (m : F ⊗ G ⟶ H) (k : H ⟶ K) (p q n : ℤ) :
    singleCochainTensorMap m p q n ≫ (CochainComplex.singleFunctor _ n).map k =
      singleCochainTensorMap (m ≫ k) p q n := by
  apply to_single_hom_ext
  apply mapBifunctor.hom_ext
  intro i j h
  change i+j=n at h
  by_cases hij : i=p ∧ j=q
  · obtain ⟨rfl,rfl⟩ := hij
    rw [comp_f,singleCochainTensorMap_same_assoc,singleCochainTensorMap_same]
    simp [CochainComplex.singleFunctor,single_map_f_self]
  · exact (singleCochainTensor_isZero_other p q i j (by tauto)).eq_of_src _ _

/-- Precomposition by the tensor of two actual single maps is retained by the single tensor map. -/
theorem singleCochainTensorMap_tensorHom {F' G' : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
    (a : F' ⟶ F) (c : G' ⟶ G) (m : F ⊗ G ⟶ H) (p q n : ℤ) :
    HomologicalComplex.tensorHom ((CochainComplex.singleFunctor _ p).map a)
        ((CochainComplex.singleFunctor _ q).map c) ≫ singleCochainTensorMap m p q n =
      singleCochainTensorMap ((a ⊗ₘ c) ≫ m) p q n := by
  apply to_single_hom_ext
  apply mapBifunctor.hom_ext
  intro i j h
  change i+j=n at h
  by_cases hij : i=p ∧ j=q
  · obtain ⟨rfl,rfl⟩ := hij
    rw [comp_f,nativeCochainTensorHom_inclusion_assoc,singleCochainTensorMap_same,
      singleCochainTensorMap_same]
    simp [CochainComplex.singleFunctor,single_map_f_self,tensorHom_comp_tensorHom_assoc]
  · exact (singleCochainTensor_isZero_other p q i j (by tauto)).eq_of_src _ _

/-- The canonical inverse inclusion of the single tensor sheaf into its specified bidegree. -/
def singleCochainTensorUnitInv (p q n : ℤ) (h : p+q=n) :
    actualSingleCochain (F ⊗ G) n ⟶
      HomologicalComplex.tensorObj (actualSingleCochain F p) (actualSingleCochain G q) :=
  mkHomFromSingle (((singleObjXSelf (ComplexShape.up ℤ) p F).inv ⊗ₘ
      (singleObjXSelf (ComplexShape.up ℤ) q G).inv) ≫
        ιTensorObj (actualSingleCochain F p) (actualSingleCochain G q) p q n h) (by
    intro k hk
    simp [singleCochainTensor_d_zero])

/-- The canonical single tensor map with the identity sheaf morphism is an actual cochain isomorphism. -/
def singleCochainTensorIso (F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (p q n : ℤ) (h : p+q=n) :
    HomologicalComplex.tensorObj (actualSingleCochain F p) (actualSingleCochain G q) ≅
      actualSingleCochain (F ⊗ G) n where
  hom := singleCochainTensorMap (𝟙 _) p q n
  inv := singleCochainTensorUnitInv p q n h
  hom_inv_id := by
    ext k : 1
    apply mapBifunctor.hom_ext
    intro i j hk
    change i+j=k at hk
    by_cases hij : i=p ∧ j=q
    · obtain ⟨rfl,rfl⟩ := hij
      obtain rfl : k=n := by omega
      rw [comp_f,singleCochainTensorMap_same_assoc,singleCochainTensorUnitInv,mkHomFromSingle_f]
      simp only [Category.id_comp,Iso.inv_hom_id_assoc,id_f,Category.comp_id]
      rw [tensorHom_comp_tensorHom_assoc]
      simp only [Iso.hom_inv_id,MonoidalCategory.id_tensorHom_id,Category.id_comp]
    · exact (singleCochainTensor_isZero_other p q i j (by tauto)).eq_of_src _ _
  inv_hom_id := by
    apply from_single_hom_ext
    rw [comp_f,singleCochainTensorUnitInv,mkHomFromSingle_f]
    simp only [Category.assoc,singleCochainTensorMap_same,id_f]
    simp only [tensorHom_comp_tensorHom_assoc,Iso.inv_hom_id,MonoidalCategory.id_tensorHom_id,
      Category.id_comp,Iso.hom_inv_id]

/-- The canonical isomorphism has the identity sheaf morphism on its specified bidegree. -/
@[simp] theorem singleCochainTensorIso_hom (p q n : ℤ) (h : p+q=n) :
    (singleCochainTensorIso F G p q n h).hom = singleCochainTensorMap (𝟙 _) p q n := rfl

/-- Every single tensor map factors through the canonical isomorphism and the actual sheaf morphism. -/
theorem singleCochainTensorMap_factor (m : F ⊗ G ⟶ H) (p q n : ℤ) (h : p+q=n) :
    singleCochainTensorMap m p q n =
      (singleCochainTensorIso F G p q n h).hom ≫ (CochainComplex.singleFunctor _ n).map m := by
  rw [singleCochainTensorIso_hom,singleCochainTensorMap_comp,Category.id_comp]

end
end BPFixedPoints.SheafTools.BinaryCells
