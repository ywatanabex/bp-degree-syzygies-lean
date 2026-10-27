import BPFixedPoints.Incidence.PublicPresheafInternalHomSheaf
import BPFixedPoints.Incidence.SchemeModuleTensor
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Original local module morphisms form the existing internal Hom sheaf

The already available natural-family internal Hom is used without changing
the original module morphisms. Its actual sections are the original
over-site morphisms, retaining every original subopen component.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1300000
variable (X : Scheme.{0}) (M N : X.Modules)

/-- The existing natural-family internal Hom is an actual abelian sheaf for the original module sheaves. -/
noncomputable def moduleHomSheaf : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} :=
  ⟨PresheafOfModules.InternalHom.presheaf (moduleCommPresheaf X M) (moduleCommPresheaf X N),
    PresheafOfModules.isSheaf_ihomObj (moduleCommPresheaf X M) (moduleCommPresheaf X N) N.isSheaf⟩

/-- An original over-site module morphism is its original compatible family on all original subopens. -/
noncomputable def moduleOverHomSection (U : X.Opens) (f : M.over U ⟶ N.over U) :
    (moduleHomSheaf X M N).obj.obj (op U) :=
  ⟨fun Y i => (f.val.app (op (Over.mk i.unop))).hom,by
    intro Y Z i j x
    have h := f.val.naturality (Over.homMk j.unop rfl :
      Over.mk (j.unop ≫ i.unop) ⟶ Over.mk i.unop).op
    exact (ConcreteCategory.congr_hom h x).symm⟩

/-- A section of the original internal Hom is the original over-site module morphism. -/
noncomputable def moduleOverHomOfSection (U : X.Opens)
    (s : (moduleHomSheaf X M N).obj.obj (op U)) : M.over U ⟶ N.over U where
  val :=
    { app Y := ModuleCat.ofHom (s.val Y.unop.hom.op)
      naturality {Y Z} i := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have h := s.property Y.unop.hom.op i.unop.left.op x
        change s.val Z.unop.hom.op (M.val.map i.unop.left.op x) =
          N.val.map i.unop.left.op (s.val Y.unop.hom.op x)
        exact (h.trans (PresheafOfModules.InternalHom.congr_app s
          (congrArg Quiver.Hom.op i.unop.w) _)).symm }

/-- The existing internal Hom sections are exactly the original local module morphisms. -/
noncomputable def moduleOverHomEquiv (U : X.Opens) :
    (M.over U ⟶ N.over U) ≃ (moduleHomSheaf X M N).obj.obj (op U) where
  toFun := moduleOverHomSection X M N U
  invFun := moduleOverHomOfSection X M N U
  left_inv f := by
    apply SheafOfModules.hom_ext
    ext Y : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  right_inv s := by
    apply PresheafOfModules.InternalHom.naturalFamilies_ext
    intro Y i x
    rfl

/-- Restricting the original Hom section is the same original over-site restriction of the morphism. -/
theorem moduleOverHomSection_restrict {U W : X.Opens} (i : W ⟶ U) (f : M.over U ⟶ N.over U) :
    (moduleHomSheaf X M N).obj.map i.op (moduleOverHomSection X M N U f) =
      moduleOverHomSection X M N W
        ((SheafOfModules.overFunctorMap X.ringCatSheaf i).inv.app M ≫
          (SheafOfModules.overMap X.ringCatSheaf i).map f ≫
            (SheafOfModules.overFunctorMap X.ringCatSheaf i).hom.app N) := by
  apply PresheafOfModules.InternalHom.naturalFamilies_ext
  intro Y j x
  rfl

/-- A global original module morphism is its original internal Hom section on the terminal open. -/
noncomputable def moduleHomTopSection (f : M ⟶ N) :
    (moduleHomSheaf X M N).obj.obj (op ⊤) :=
  ⟨fun Y _ => (f.val.app Y).hom,by
    intro Y Z i j x
    exact (ConcreteCategory.congr_hom (f.val.naturality j) x).symm⟩

/-- The original terminal internal Hom section evaluates to the original global module morphism. -/
noncomputable def moduleHomOfTopSection
    (s : (moduleHomSheaf X M N).obj.obj (op ⊤)) : M ⟶ N where
  val :=
    { app Y := ModuleCat.ofHom (s.val (homOfLE (show Y.unop ≤ ⊤ from le_top)).op)
      naturality {Y Z} i := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        have h := s.property (homOfLE (show Y.unop ≤ ⊤ from le_top)).op i x
        change s.val (homOfLE (show Z.unop ≤ ⊤ from le_top)).op (M.val.map i x) =
          N.val.map i (s.val (homOfLE (show Y.unop ≤ ⊤ from le_top)).op x)
        exact (h.trans (PresheafOfModules.InternalHom.congr_app s (Subsingleton.elim _ _) _)).symm }

/-- Original global module morphisms are precisely the actual terminal sections of the existing internal Hom sheaf. -/
noncomputable def moduleHomTopEquiv : (M ⟶ N) ≃ (moduleHomSheaf X M N).obj.obj (op ⊤) where
  toFun := moduleHomTopSection X M N
  invFun := moduleHomOfTopSection X M N
  left_inv f := by
    apply SheafOfModules.hom_ext
    ext Y : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  right_inv s := by
    apply PresheafOfModules.InternalHom.naturalFamilies_ext
    intro Y i x
    exact PresheafOfModules.InternalHom.congr_app s (Subsingleton.elim _ _) x

/-- The original global morphism restricts to exactly the original over-site morphism. -/
theorem moduleHomTopSection_restrict (U : X.Opens) (f : M ⟶ N) :
    (moduleHomSheaf X M N).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (moduleHomTopSection X M N f) =
        moduleOverHomSection X M N U ((SheafOfModules.overFunctor X.ringCatSheaf U).map f) := by
  apply PresheafOfModules.InternalHom.naturalFamilies_ext
  intro Y i x
  rfl

end BPFixedPoints.SheafTools
