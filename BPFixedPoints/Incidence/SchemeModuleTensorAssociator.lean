import BPFixedPoints.Incidence.SchemeModuleMonoidalSections
import BPFixedPoints.Incidence.SchemeModuleFiniteTensor

/-! # Reassociation of the original tensor sheaves

The original sheafification tensors are retained. Their reassociation is
obtained from Mathlib's coherent associator, and its value on the original
pure sections is computed using the native adjoint tensorator.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (X : Scheme.{0})

/-- Compare the original left-associated tensor to the coherent left-associated tensor. -/
noncomputable def moduleTensorLeftTripleIso (M N P : X.Modules) :
    moduleTensor X (moduleTensor X M N) P ≅ (M ⊗ N) ⊗ P :=
  moduleTensorIsoMonoidal X _ _ ≪≫ (moduleTensorIsoMonoidal X M N ⊗ᵢ Iso.refl P)

/-- Compare the original right-associated tensor to the coherent right-associated tensor. -/
noncomputable def moduleTensorRightTripleIso (M N P : X.Modules) :
    moduleTensor X M (moduleTensor X N P) ≅ M ⊗ (N ⊗ P) :=
  moduleTensorIsoMonoidal X _ _ ≪≫ (Iso.refl M ⊗ᵢ moduleTensorIsoMonoidal X N P)

/-- Reassociate the actual original tensor sheaves by the coherent native associator. -/
noncomputable def moduleTensorAssociator (M N P : X.Modules) :
    moduleTensor X (moduleTensor X M N) P ≅ moduleTensor X M (moduleTensor X N P) :=
  moduleTensorLeftTripleIso X M N P ≪≫ α_ M N P ≪≫ (moduleTensorRightTripleIso X M N P).symm

/-- The reassociation is the native associator under the original tensor comparisons. -/
theorem moduleTensorAssociator_comparison (M N P : X.Modules) :
    (moduleTensorAssociator X M N P).hom ≫ (moduleTensorRightTripleIso X M N P).hom =
      (moduleTensorLeftTripleIso X M N P).hom ≫ (α_ M N P).hom := by
  simp [moduleTensorAssociator]

/-- Original left-nested pure sections map to the native left-nested pure sections. -/
theorem moduleTensorLeftTripleIso_pure (M N P : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) (z : Γ(P, U)) :
    (moduleTensorLeftTripleIso X M N P).hom.app U
      (moduleTensorPureSection X (moduleTensor X M N) P U
        (moduleTensorPureSection X M N U x y) z) =
      moduleMonoidalPureSection X (M ⊗ N) P U
        (moduleMonoidalPureSection X M N U x y) z := by
  change ((moduleTensorIsoMonoidal X M N).hom ⊗ₘ 𝟙 P).app U
    ((moduleTensorIsoMonoidal X (moduleTensor X M N) P).hom.app U _) = _
  rw [moduleTensorIsoMonoidal_pure, moduleMonoidalPureSection_map,
    moduleTensorIsoMonoidal_pure]
  rfl

/-- Original right-nested pure sections map to the native right-nested pure sections. -/
theorem moduleTensorRightTripleIso_pure (M N P : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) (z : Γ(P, U)) :
    (moduleTensorRightTripleIso X M N P).hom.app U
      (moduleTensorPureSection X M (moduleTensor X N P) U x
        (moduleTensorPureSection X N P U y z)) =
      moduleMonoidalPureSection X M (N ⊗ P) U x
        (moduleMonoidalPureSection X N P U y z) := by
  change (𝟙 M ⊗ₘ (moduleTensorIsoMonoidal X N P).hom).app U
    ((moduleTensorIsoMonoidal X M (moduleTensor X N P)).hom.app U _) = _
  rw [moduleTensorIsoMonoidal_pure, moduleMonoidalPureSection_map,
    moduleTensorIsoMonoidal_pure]
  rfl

/-- Reassociation preserves the three original pure section factors in their original order. -/
theorem moduleTensorAssociator_pure (M N P : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) (z : Γ(P, U)) :
    (moduleTensorAssociator X M N P).hom.app U
      (moduleTensorPureSection X (moduleTensor X M N) P U
        (moduleTensorPureSection X M N U x y) z) =
      moduleTensorPureSection X M (moduleTensor X N P) U x
        (moduleTensorPureSection X N P U y z) := by
  let e := moduleTensorRightTripleIso X M N P
  have he (s : Γ(moduleTensor X M (moduleTensor X N P), U)) :
      e.inv.app U (e.hom.app U s) = s :=
    congrArg (fun k => k.app U s) e.hom_inv_id
  have hi : Function.Injective (fun s : Γ(moduleTensor X M (moduleTensor X N P), U) =>
      e.hom.app U s) := fun s t hst =>
    (he s).symm.trans ((congrArg (fun q => e.inv.app U q) hst).trans (he t))
  apply hi
  have h := congrArg (fun k => k.app U
    (moduleTensorPureSection X (moduleTensor X M N) P U
      (moduleTensorPureSection X M N U x y) z))
        (moduleTensorAssociator_comparison X M N P)
  simp only [Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply] at h
  change (moduleTensorRightTripleIso X M N P).hom.app U
    ((moduleTensorAssociator X M N P).hom.app U _) =
      (moduleTensorRightTripleIso X M N P).hom.app U _
  rw [h, moduleTensorLeftTripleIso_pure, moduleTensorRightTripleIso_pure,
    moduleMonoidalPureSection_assoc]

end BPFixedPoints.SheafTools
