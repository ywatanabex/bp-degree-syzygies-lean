import BPFixedPoints.Incidence.BinaryCoverCellActualTensor
import BPFixedPoints.Incidence.AbelianSheafTensorEvaluation

/-! # Native tensor comparison on original presheaf sections

The native monoidal sheafification adjunction compares each original
presheaf pure tensor with the actual pure sections of its two original
images. No claim that arbitrary sheaf sections lift globally is needed.
-/

namespace BPFixedPoints.SheafTools.AbelianTensor
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Functor TopologicalSpace Opposite
open scoped BPFixedPoints.SheafTools.AbelianTensor TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
noncomputable section
variable {T : Type} [TopologicalSpace T]

/-- The original unit and native tensorator retain pure presheaf representatives. -/
theorem sheafification_tensor_pure (P Q : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{0})
    (W : Opens T) (x : P.obj (op W)) (y : Q.obj (op W)) :
    ((Functor.Monoidal.μIso (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) P Q).inv.hom.app (op W))
      (((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app (P ⊗ Q)).app (op W)
        (groupPure (P.obj (op W)) (Q.obj (op W)) x y)) =
      sheafPureSection _ _ W (((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app P).app (op W) x)
        (((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app Q).app (op W) y) := by
  have h := ConcreteCategory.congr_hom (congrArg (fun a => a.app (op W))
    ((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit_app_tensor_comp_map_δ P Q))
      (groupPure (P.obj (op W)) (Q.obj (op W)) x y)
  change _ = (LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) _ _).app (op W)
    ((((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app P).app (op W) ⊗ₘ
      ((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app Q).app (op W))
        (groupPure (P.obj (op W)) (Q.obj (op W)) x y)) at h
  have e := groupPure_map (P.obj (op W)) (Q.obj (op W)) (((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app P).app (op W))
    (((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app Q).app (op W)) x y
  exact h.trans (congrArg (fun z =>
    (LaxMonoidal.μ (sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) _ _).app (op W) z) e)

/-- Forgetting the native integer module tensor retains each original pure tensor. -/
theorem integerForget_tensor_pure (A B : ModuleCat.{0} ℤ) (x : A) (y : B) :
    (Functor.Monoidal.μIso (forget₂ (ModuleCat.{0} ℤ) AddCommGrpCat.{0}) A B).hom
      (groupPure _ _ x y) = x ⊗ₜ[ℤ] y := by
  change (integerModuleEquivalence.counitIso.inv.app _ ≫
    integerModuleEquivalence.functor.map
      ((integerModuleEquivalence.unitIso.app _).inv ≫
        (integerModuleEquivalence.unitIso.inv.app A ⊗ₘ integerModuleEquivalence.unitIso.inv.app B)))
          (groupPure _ _ x y) = _
  rw [Functor.map_comp]
  change (integerModuleEquivalence.functor.map
      (integerModuleEquivalence.unitIso.inv.app A ⊗ₘ integerModuleEquivalence.unitIso.inv.app B))
    ((integerModuleEquivalence.counitIso.inv.app _ ≫
      integerModuleEquivalence.functor.map ((integerModuleEquivalence.unitIso.app _).inv))
        (groupPure _ _ x y)) = _
  have e : integerModuleEquivalence.counitIso.inv.app (integerModuleEquivalence.functor.obj
      ((integerModuleEquivalence.functor ⋙ integerModuleEquivalence.inverse).obj A ⊗
        (integerModuleEquivalence.functor ⋙ integerModuleEquivalence.inverse).obj B)) ≫
      integerModuleEquivalence.functor.map ((integerModuleEquivalence.unitIso.app _).inv) = 𝟙 _ :=
    integerModuleEquivalence.counitInv_functor_comp _
  rw [e]
  change TensorProduct.map (integerModuleEquivalence.unitIso.inv.app A).hom
    (integerModuleEquivalence.unitIso.inv.app B).hom (_ ⊗ₜ[ℤ] _) = _
  rw [TensorProduct.map_tmul]
  congr 1
  · change integerModuleEquivalence.unitIso.inv.app A
      ((integerModuleEquivalence.counitIso.inv.app (integerModuleEquivalence.functor.obj A)) x) = x
    rw [integerModuleEquivalence.counitInv_app_functor]
    exact ConcreteCategory.congr_hom (integerModuleEquivalence.unitIso.hom_inv_id_app A) x
  · change integerModuleEquivalence.unitIso.inv.app B
      ((integerModuleEquivalence.counitIso.inv.app (integerModuleEquivalence.functor.obj B)) y) = y
    rw [integerModuleEquivalence.counitInv_app_functor]
    exact ConcreteCategory.congr_hom (integerModuleEquivalence.unitIso.hom_inv_id_app B) y

/-- Native integer forgetting and sheafification retain original pure representatives. -/
theorem integerSheafification_tensor_pure
    (P Q : (Opens T)ᵒᵖ ⥤ ModuleCat.{0} ℤ) (W : Opens T)
    (x : P.obj (op W)) (y : Q.obj (op W)) :
    (Functor.Monoidal.μIso BinaryCells.integerSheafification P Q).hom.hom.app (op W)
      (sheafPureSection _ _ W
        (((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app
          (BinaryCells.toAbelianPresheaf.obj P)).app (op W) x)
        (((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app
          (BinaryCells.toAbelianPresheaf.obj Q)).app (op W) y)) =
      ((sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}).unit.app
        (BinaryCells.toAbelianPresheaf.obj (P ⊗ Q))).app (op W) (x ⊗ₜ[ℤ] y) := by
  let L := presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}
  let adj := sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{0}
  let FP := BinaryCells.toAbelianPresheaf.obj P
  let FQ := BinaryCells.toAbelianPresheaf.obj Q
  have h := sheafification_tensor_pure FP FQ W x y
  have he : (Functor.Monoidal.μIso L FP FQ).hom.hom.app (op W)
      (sheafPureSection _ _ W ((adj.unit.app FP).app (op W) x) ((adj.unit.app FQ).app (op W) y)) =
        (adj.unit.app (FP ⊗ FQ)).app (op W) (groupPure (FP.obj (op W)) (FQ.obj (op W)) x y) := by
    rw [← h, ← ConcreteCategory.comp_apply]
    have e := congrArg (fun f => f.hom.app (op W)) (Functor.Monoidal.μIso L FP FQ).inv_hom_id
    exact ConcreteCategory.congr_hom e _
  have hn := ConcreteCategory.congr_hom (congrArg (fun f => f.app (op W))
    (adj.unit.naturality (LaxMonoidal.μ BinaryCells.toAbelianPresheaf P Q)))
      (groupPure (FP.obj (op W)) (FQ.obj (op W)) x y)
  have hp := congrArg ((adj.unit.app (BinaryCells.toAbelianPresheaf.obj (P ⊗ Q))).app (op W))
    (integerForget_tensor_pure (P.obj (op W)) (Q.obj (op W)) x y)
  exact (congrArg (fun z => (L.map (LaxMonoidal.μ BinaryCells.toAbelianPresheaf P Q)).hom.app (op W) z) he).trans
    (hn.symm.trans hp)

end
end BPFixedPoints.SheafTools.AbelianTensor
