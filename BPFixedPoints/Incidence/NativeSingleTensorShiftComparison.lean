import BPFixedPoints.Incidence.NativeCochainTensorShifts

/-! # Original single-degree pairings and Mathlib's native tensor shifts

The ordered native right-then-left shift pairing is compared with the
original coefficient pairing as an equality of entire cochain maps.
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
local instance singleTensorShiftComparisonSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
variable (b : SectionPairing F G H)

/-- The original degree-zero pairing after Mathlib's ordered native right and left tensor shifts. -/
def nativeShiftedSinglePairing (i j : ℤ) :
    HomologicalComplex.tensorObj ((actualSingleCochain F 0)⟦i⟧) ((actualSingleCochain G 0)⟦j⟧) ⟶
      (actualSingleCochain H 0)⟦i+j⟧ :=
  (nativeTensorShiftRightIso (actualSingleCochain F 0) (actualSingleCochain G 0) i j).hom ≫
    (singleCochainTensorPairingMap b 0 0 0)⟦i+j⟧'

/-- Conjugate the native shifted pairing by Mathlib's original single-degree shift isomorphisms. -/
def nativeSingleShiftTensorPairing (i j : ℤ) :
    HomologicalComplex.tensorObj (actualSingleCochain F (-i)) (actualSingleCochain G (-j)) ⟶
      actualSingleCochain H (-(i+j)) :=
  HomologicalComplex.tensorHom
    (((CochainComplex.singleFunctors _).shiftIso i (-i) 0 (by omega)).inv.app F)
    (((CochainComplex.singleFunctors _).shiftIso j (-j) 0 (by omega)).inv.app G) ≫
      nativeShiftedSinglePairing b i j ≫
        ((CochainComplex.singleFunctors _).shiftIso (i+j) (-(i+j)) 0 (by omega)).hom.app H

private theorem integerTensorHom_inclusion
    {K L M N : CochainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℤ}
    (f : K ⟶ M) (g : L ⟶ N) (p q n : ℤ) (h : p+q=n) :
    ιTensorObj K L p q n h ≫ (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫ ιTensorObj M N p q n h := by
  simpa only [curriedTensor_map_app,curriedTensor_obj_map,MonoidalCategory.tensorHom_def,Category.assoc] using
    (ι_mapBifunctorMap f g (curriedTensor _) (ComplexShape.up ℤ) p q n h)

private theorem zeroPairing_eqToHom (p q n : ℤ) (hp : p=0) (hq : q=0) (hn : n=0)
    (h : p+q=n) {A B C : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
    (hA : A=(actualSingleCochain F 0).X p) (hB : B=(actualSingleCochain G 0).X q)
    (hC : (actualSingleCochain H 0).X n=C) :
    (eqToHom hA ⊗ₘ eqToHom hB) ≫
      ιTensorObj (actualSingleCochain F 0) (actualSingleCochain G 0) p q n h ≫
        (singleCochainTensorPairingMap b 0 0 0).f n ≫ eqToHom hC =
    ((eqToHom (hA.trans (congrArg (actualSingleCochain F 0).X hp)) ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 F).hom) ⊗ₘ
      (eqToHom (hB.trans (congrArg (actualSingleCochain G 0).X hq)) ≫
        (singleObjXSelf (ComplexShape.up ℤ) 0 G).hom)) ≫ b.sheafMap ≫
      (singleObjXSelf (ComplexShape.up ℤ) 0 H).inv ≫
        eqToHom ((congrArg (actualSingleCochain H 0).X hn).symm.trans hC) := by
  subst p
  subst q
  subst n
  rw [singleCochainTensorPairingMap_same_assoc b 0 0 0 rfl]
  simp only [Category.assoc,← tensorHom_comp_tensorHom]

/-- Mathlib's ordered native tensor shifts differ from the original negative single-degree pairing by exactly the Koszul crossing sign. -/
theorem nativeSingleShiftTensorPairing_eq (i j : ℤ) :
    nativeSingleShiftTensorPairing b i j =
      (i*j).negOnePow • singleCochainTensorPairingMap b (-i) (-j) (-(i+j)) := by
  apply to_single_hom_ext
  simp only [nativeSingleShiftTensorPairing,nativeShiftedSinglePairing,comp_f,units_smul_f_apply,
    CochainComplex.shiftFunctor_map_f']
  apply mapBifunctor.hom_ext
  intro p q h
  by_cases hp : p= -i
  · subst p
    have hq : q= -j := by change -i+q= -(i+j) at h; omega
    subst q
    rw [← Category.assoc,integerTensorHom_inclusion]
    simp only [Category.assoc]
    erw [nativeTensorShiftRightIso_inclusion_assoc (actualSingleCochain F 0)
      (actualSingleCochain G 0) i j (-i) (-j) (-(i+j)) h]
    simp only [Int.neg_mul,Int.negOnePow_neg,Linear.comp_units_smul,
      Linear.units_smul_comp]
    dsimp only [NatIso.ofComponents,Hom.isoOfComponents]
    simp only [Functor.comp_obj,eqToIso.hom,eqToIso.inv]
    erw [zeroPairing_eqToHom b (-i+i) (-j+j) (-(i+j)+(i+j)) (by omega) (by omega) (by omega),
      singleCochainTensorPairingMap_same b (-i) (-j) (-(i+j)) h]
    simp [singleObjXSelf,singleObjXIsoOfEq,-tensorHom_comp_tensorHom]
  · have hz := (tensorRight ((actualSingleCochain G (-j)).X q)).map_isZero
      (isZero_single_obj_X (ComplexShape.up ℤ) (-i) F p hp)
    exact hz.eq_of_src _ _

/-- Two degree-one input classes retain the negative native shift crossing sign over the original integer sheaf tensor. -/
theorem nativeSingleShiftTensorPairing_one_one :
    nativeSingleShiftTensorPairing b 1 1 = -singleCochainTensorPairingMap b (-1) (-1) (-2) := by
  simpa using nativeSingleShiftTensorPairing_eq b 1 1

end
end BPFixedPoints.SheafTools.BinaryCells
