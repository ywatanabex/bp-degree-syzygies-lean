import BPFixedPoints.Incidence.ResolutionSuccessorSyzygyCone

/-! # Native Hom cocycle composition retains the specified shifted morphisms

This is a representative calculation for Mathlib's original Hom cochains,
right shifts and shifted composition. No cohomology model is introduced.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex CochainComplex.HomComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M : CochainComplex C ℤ}

/-- The native right-shifted cocycle map retains its original coefficient in every degree. -/
theorem nativeHomShift_component {n : ℤ} (x : Cocycle K L n) (p : ℤ) :
    (Cocycle.equivHomShift.symm x).f p = x.val.v p (p+n) rfl := by
  simp [Cocycle.equivHomShift_symm_apply,Cocycle.homOf_f,Cocycle.rightShift_coe,
    Cochain.rightShift_v _ n 0 (zero_add n) p p (add_zero p) (p+n) rfl,
    CochainComplex.shiftFunctorObjXIso]

private theorem cochain_v_cast {n : ℤ} (x : Cochain L M n) (p q q' : ℤ)
    (hpq : p+n=q) (hqq' : q=q') :
    x.v p q hpq ≫ eqToHom (congrArg M.X hqq') = x.v p q' (hpq.trans hqq') := by
  subst q'
  simp

/-- Native shifted composition is precisely the original Hom-cochain composition, including all shift identifications. -/
theorem nativeHomShift_comp {n m t : ℤ} (x : Cocycle K L n) (y : Cocycle L M m)
    (z : Cocycle K M t) (h : m+n=t) (hz : x.val.comp y.val (by omega : n+m=t)=z.val) :
    ShiftedHom.comp (Cocycle.equivHomShift.symm x) (Cocycle.equivHomShift.symm y) h =
      Cocycle.equivHomShift.symm z := by
  subst t
  ext p
  simp only [ShiftedHom.comp,comp_f,CochainComplex.shiftFunctor_map_f',nativeHomShift_component,
    CochainComplex.shiftFunctorAdd'_inv_app_f']
  have hc := Cochain.congr_v hz p (p+(m+n)) rfl
  rw [Cochain.comp_v _ _ (by omega : n+m=m+n) p (p+n) (p+(m+n)) rfl (by omega)] at hc
  dsimp only [HomologicalComplex.XIsoOfEq,eqToIso]
  rw [cochain_v_cast y.val (p+n) (p+n+m) (p+(m+n)) rfl (by omega)]
  exact hc

/-- A native cocycle to the original single complex is the original coefficient map followed by its native single shift. -/
theorem nativeHomShift_single (n : ℤ) {Y : C} (x : K.X (-n) ⟶ Y)
    (hx : K.d (-n-1) (-n) ≫ x=0) :
    Cocycle.equivHomShift.symm (Cocycle.toSingleMk x (by omega : -n+n=0) (-n-1) (by omega) hx) =
      mkHomToSingle x (by
        intro p hp
        have hp' : p = -n-1 := by change p+1= -n at hp; omega
        subst p
        exact hx) ≫
          ((CochainComplex.singleFunctors C).shiftIso n (-n) 0 (by omega)).inv.app Y := by
  apply (cancel_mono (((CochainComplex.singleFunctors C).shiftIso n (-n) 0 (by omega)).hom.app Y)).mp
  simp only [Category.assoc,Iso.inv_hom_id_app,Category.comp_id]
  apply to_single_hom_ext
  simp only [comp_f,nativeHomShift_component]
  simp [Cocycle.toSingleMk,Cochain.toSingleMk,Cochain.single,Cochain.v,Cochain.mk,
    singleObjXSelf,singleObjXIsoOfEq,
    HomologicalComplex.XIsoOfEq,Category.assoc]

/-- A specified native cocycle with the original single-map coefficient retains that entire original single map and its shift. -/
theorem nativeHomShift_single_of_coefficient (n : ℤ) {Y : C}
    (f : K ⟶ (CochainComplex.singleFunctor C (-n)).obj Y)
    (z : Cocycle K ((CochainComplex.singleFunctor C 0).obj Y) n)
    (hz : z.val = Cochain.toSingleMk
      (f.f (-n) ≫ (singleObjXSelf (ComplexShape.up ℤ) (-n) Y).hom) (by omega : -n+n=0)) :
    Cocycle.equivHomShift.symm z =
      f ≫ ((CochainComplex.singleFunctors C).shiftIso n (-n) 0 (by omega)).inv.app Y := by
  let x := f.f (-n) ≫ (singleObjXSelf (ComplexShape.up ℤ) (-n) Y).hom
  have hx : K.d (-n-1) (-n) ≫ x=0 := by
    dsimp only [x]
    rw [← Category.assoc,← f.comm]
    simp
  have hz' : z=Cocycle.toSingleMk x (by omega : -n+n=0) (-n-1) (by omega) hx := Cocycle.ext hz
  rw [hz',nativeHomShift_single]
  congr 1
  apply to_single_hom_ext
  simp [x,mkHomToSingle_f,Category.assoc]

end
end BPFixedPoints.ExtResolutionTools
