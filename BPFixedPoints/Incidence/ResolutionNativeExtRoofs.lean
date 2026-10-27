import BPFixedPoints.Incidence.ResolutionNativeRoofs
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-! # Native Ext classes of the original augmentation roofs

The native derived-category roof and the native shift identification are
used directly. Equality with the iterated Yoneda comparison in positive
degree is not imposed by a new definition of that comparison.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
universe w w' v u
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w'} C]
variable (P : ChainComplex C ℕ) {A : C} (π : P.X 0 ⟶ A) (z : P.d 1 0 ≫ π=0)
variable (e : (ShortComplex.mk (P.d 1 0) π z).Exact) [Epi π] (hP : ∀ n, P.ExactAt (n+1))

/-- The original native roof, viewed in Mathlib's original Ext through its native shift isomorphism. -/
def nativeCocycleExt {Y : C} (n : ℕ) (x : P.X n ⟶ Y) (hx : P.d (n+1) n ≫ x=0) : Ext.{w'} A Y n :=
  Ext.homEquiv.symm
    (nativeCocycleRoof P π z e hP n x hx ≫
      ((DerivedCategory.singleFunctors C).shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).inv.app Y)

/-- Every original native roof retains exactly its original derived-category morphism and native shift. -/
theorem nativeCocycleExt_hom {Y : C} (n : ℕ) (x : P.X n ⟶ Y) (hx : P.d (n+1) n ≫ x=0) :
    (nativeCocycleExt P π z e hP n x hx).hom =
      nativeCocycleRoof P π z e hP n x hx ≫
        ((DerivedCategory.singleFunctors C).shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).inv.app Y :=
  Ext.homEquiv.apply_symm_apply _

/-- The native degree-zero Ext roof of an original augmentation factorization is the original degree-zero Ext morphism. -/
theorem nativeCocycleExt_zero_factor {Y : C} (g : A ⟶ Y) (hx : P.d 1 0 ≫ (π ≫ g)=0) :
    nativeCocycleExt P π z e hP 0 (π ≫ g) hx=Ext.mk₀ g := by
  apply Ext.ext
  rw [nativeCocycleExt_hom,nativeCocycleRoof_zero_factor,Ext.mk₀_hom]
  change DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map g) ≫
    ((DerivedCategory.singleFunctors C).shiftIso 0 0 0 (zero_add 0)).inv.app Y = _
  rw [SingleFunctors.shiftIso_zero_inv_app]
  simp [ShiftedHom.mk₀,shiftFunctorZero']
  rfl

variable {P} {Q : ChainComplex C ℕ} (f : P ⟶ Q)
variable {B : C} (πQ : Q.X 0 ⟶ B) (zQ : Q.d 1 0 ≫ πQ=0)
variable (eQ : (ShortComplex.mk (Q.d 1 0) πQ zQ).Exact) [Epi πQ] (hQ : ∀ n, Q.ExactAt (n+1))

/-- The native Ext roofs preserve original augmentation squares in every degree. -/
theorem nativeCocycleExt_source (a : A ⟶ B) (ha : f.f 0 ≫ πQ=π ≫ a)
    {Y : C} (n : ℕ) (x : Q.X n ⟶ Y) (hx : Q.d (n+1) n ≫ x=0)
    (hfx : P.d (n+1) n ≫ (f.f n ≫ x)=0) :
    nativeCocycleExt P π z e hP n (f.f n ≫ x) hfx =
      (Ext.mk₀ a).comp (nativeCocycleExt Q πQ zQ eQ hQ n x hx) (zero_add n) := by
  apply Ext.ext
  rw [nativeCocycleExt_hom,nativeCocycleRoof_source π z e hP f πQ zQ eQ hQ a ha n x hx hfx,
    Ext.comp_hom,Ext.mk₀_hom,nativeCocycleExt_hom,ShiftedHom.mk₀_comp]
  rw [Category.assoc]
  rfl

end
end BPFixedPoints.ExtResolutionTools
