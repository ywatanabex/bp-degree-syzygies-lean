import BPFixedPoints.Incidence.NativeCochainSingleTensorPairing

/-! # The actual ordered tensor shifts of native cochain complexes

Mathlib's existing right-variable shift is followed by its left-variable
shift. The original bidegree inclusion retains the actual Koszul factor.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open TopologicalSpace Opposite AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable {T : Type} [TopologicalSpace T]
local instance cochainTensorShiftSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
variable (K L : CochainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℤ)

/-- Mathlib's original right-variable shift followed by its original left-variable shift and native sum shift. -/
def nativeTensorShiftRightIso (i j : ℤ) :
    HomologicalComplex.tensorObj (K⟦i⟧) (L⟦j⟧) ≅ (HomologicalComplex.tensorObj K L)⟦i+j⟧ :=
  CochainComplex.mapBifunctorShift₂Iso (K⟦i⟧) L (curriedTensor _) j ≪≫
    (shiftFunctor _ j).mapIso (CochainComplex.mapBifunctorShift₁Iso K L (curriedTensor _) i) ≪≫
      (shiftFunctorAdd' _ i j (i+j) rfl).symm.app (HomologicalComplex.tensorObj K L)

private theorem tensorInclusion_cast (p q n n' : ℤ) (h : p+q=n) (e : n=n') :
    ιTensorObj K L p q n h ≫ eqToHom (congrArg (HomologicalComplex.tensorObj K L).X e) =
      ιTensorObj K L p q n' (h.trans e) := by
  subst n'
  simp

/-- Every original bidegree inclusion keeps Mathlib's actual right-shift factor, with all native sum-shift identifications. -/
@[reassoc] theorem nativeTensorShiftRightIso_inclusion (i j p q n : ℤ) (h : p+q=n) :
    ιTensorObj (K⟦i⟧) (L⟦j⟧) p q n h ≫ (nativeTensorShiftRightIso K L i j).hom.f n =
      (p*j).negOnePow • ιTensorObj K L (p+i) (q+j) (n+(i+j)) (by omega) := by
  simp only [nativeTensorShiftRightIso,Iso.trans_hom,Iso.symm_hom,Iso.app_inv,
    Functor.mapIso_hom,comp_f,CochainComplex.shiftFunctor_map_f']
  rw [← Category.assoc,← Category.assoc,
    CochainComplex.ι_mapBifunctorShift₂Iso_hom_f (K⟦i⟧) L (curriedTensor _) j p q n h
      (q+j) (n+j) rfl rfl]
  simp only [CochainComplex.shiftFunctorObjXIso,HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom,Functor.map_id,Category.id_comp,Linear.units_smul_comp,Category.assoc]
  simp only [Iso.refl_inv,Functor.map_id,Category.id_comp,Category.comp_id]
  rw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc K L (curriedTensor _) i p (q+j) (n+j)
    (by omega) (p+i) (n+j+i) rfl rfl]
  simp only [CochainComplex.shiftFunctorObjXIso,HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom,Iso.refl_inv,Functor.map_id,NatTrans.id_app,Category.id_comp,Category.comp_id,
    Iso.app_hom,Iso.symm_hom,CochainComplex.shiftFunctorAdd'_inv_app_f']
  simp only [HomologicalComplex.XIsoOfEq,eqToIso,eqToHom_refl,Functor.map_id,NatTrans.id_app,
    Category.id_comp,Category.comp_id,Category.assoc,eqToHom_trans]
  rw [tensorInclusion_cast]
  · simp [curriedTensor_obj_map,curriedTensor_map_app]
  · omega

end
end BPFixedPoints.SheafTools.BinaryCells
