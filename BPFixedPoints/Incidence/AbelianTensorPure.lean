import BPFixedPoints.Incidence.AbelianSheafTensor

/-! # Pure tensors and bilinear evaluation in the native integer tensor

The native integer-module equivalence supplies the tensor and its pure
sections. Bilinear evaluation retains the original group elements through
the original counit, independently of any cohomology coordinates.
-/

namespace BPFixedPoints.SheafTools.AbelianTensor
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BPFixedPoints.SheafTools.AbelianTensor TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
noncomputable section
variable (A B C : AddCommGrpCat.{0})

/-- The pure tensor in the native transported integer tensor uses the original counit inverse. -/
def groupPure (x : A) (y : B) : (A ⊗ B : AddCommGrpCat) :=
  (integerModuleEquivalence.counitIso.inv.app A).hom x ⊗ₜ[ℤ]
    (integerModuleEquivalence.counitIso.inv.app B).hom y

/-- The original counit is integer linear for the original module structure. -/
def groupCounitLinear : integerModuleEquivalence.inverse.obj A →ₗ[ℤ] A where
  toFun := (integerModuleEquivalence.counitIso.hom.app A).hom
  map_add' := map_add _
  map_smul' r x := by
    convert! AddMonoidHom.map_zsmul (integerModuleEquivalence.counitIso.hom.app A).hom r x using 1 <;>
      first | apply int_smul_eq_zsmul | congr 1; apply int_smul_eq_zsmul

/-- The original biadditive map is canonically integer bilinear. -/
def groupOriginalBilinear (b : A →+ B →+ C) : A →ₗ[ℤ] B →ₗ[ℤ] C where
  toFun x := (b x).toIntLinearMap
  map_add' := by intro x y; ext z; exact congrArg (fun h : B →+ C => h z) (b.map_add x y)
  map_smul' := by intro r x; ext y; exact congrArg (fun h : B →+ C => h y) (map_zsmul b r x)

/-- Pull the original biadditive pairing back along the original integer-module counits. -/
def groupBilinear (b : A →+ B →+ C) :
    integerModuleEquivalence.inverse.obj A →ₗ[ℤ]
      integerModuleEquivalence.inverse.obj B →ₗ[ℤ] C :=
  (groupOriginalBilinear A B C b).compl₁₂ (groupCounitLinear A) (groupCounitLinear B)

/-- Native integer-tensor evaluation of the original biadditive pairing. -/
def groupLift (b : A →+ B →+ C) : A ⊗ B ⟶ C :=
  AddCommGrpCat.ofHom (TensorProduct.lift (groupBilinear A B C b)).toAddMonoidHom

/-- Evaluating a pure tensor gives exactly the original pairing of the original elements. -/
theorem groupLift_pure (b : A →+ B →+ C) (x : A) (y : B) :
    groupLift A B C b (groupPure A B x y) = b x y := by
  change TensorProduct.lift (groupBilinear A B C b) (_ ⊗ₜ[ℤ] _) = _
  rw [TensorProduct.lift.tmul]
  change b (integerModuleEquivalence.counitIso.hom.app A
      ((integerModuleEquivalence.counitIso.inv.app A).hom x))
    (integerModuleEquivalence.counitIso.hom.app B
      ((integerModuleEquivalence.counitIso.inv.app B).hom y)) = _
  simp only [← ConcreteCategory.comp_apply,Iso.inv_hom_id_app]
  rfl

/-- Morphisms from the native group tensor are determined by the original pure elements. -/
theorem groupTensor_hom_ext {f g : A ⊗ B ⟶ C}
    (h : ∀ x y, f (groupPure A B x y) = g (groupPure A B x y)) : f = g := by
  apply AddCommGrpCat.ext
  intro z
  change f.hom z = g.hom z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    have he := h (integerModuleEquivalence.counitIso.hom.app A x)
      (integerModuleEquivalence.counitIso.hom.app B y)
    simpa only [groupPure,← ConcreteCategory.comp_apply,Iso.hom_inv_id_app,ConcreteCategory.id_apply] using he
  | add x y hx hy => simp only [map_add,hx,hy]

/-- Every original group morphism retains the native pure tensor of its two original images. -/
theorem groupPure_map {A' B' : AddCommGrpCat.{0}} (f : A ⟶ A') (g : B ⟶ B')
    (x : A) (y : B) :
    (f ⊗ₘ g) (groupPure A B x y) = groupPure A' B' (f x) (g y) := by
  change TensorProduct.map (integerModuleEquivalence.inverse.map f).hom
    (integerModuleEquivalence.inverse.map g).hom (_ ⊗ₜ[ℤ] _) = _
  rw [TensorProduct.map_tmul]
  have hf := ConcreteCategory.congr_hom (integerModuleEquivalence.counitIso.inv.naturality f) x
  have hg := ConcreteCategory.congr_hom (integerModuleEquivalence.counitIso.inv.naturality g) y
  exact congrArg₂ (fun a b => a ⊗ₜ[ℤ] b) hf.symm hg.symm

end
end BPFixedPoints.SheafTools.AbelianTensor
