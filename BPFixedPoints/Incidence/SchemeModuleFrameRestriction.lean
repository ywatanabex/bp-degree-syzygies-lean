import BPFixedPoints.Incidence.SchemeModuleTensorFrameTransitions

/-! # Original tensor frames and native over-site restrictions

All comparisons use the original scheme modules and Mathlib functors.
The coefficient face atlas and derived-cohomology comparisons are separate.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (X : Scheme.{0})

/-- The specified original frame restricted by the native over-site functors. -/
noncomputable def moduleOverFrameRestriction {U W : X.Opens} (i : W ⟶ U) (M : X.Modules)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W) :=
  (SheafOfModules.overFunctorMap X.ringCatSheaf i).symm.app M ≪≫
    (SheafOfModules.overMap X.ringCatSheaf i).mapIso e ≪≫
      SheafOfModules.overMapUnitIso (R := X.ringCatSheaf) i

/-- The restricted frame retains the original section values on every subopen. -/
theorem moduleOverFrameRestriction_apply {U W : X.Opens} (i : W ⟶ U) (M : X.Modules)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (S : Over W)
    (x : Γ(M, S.left)) :
    (show Γ(X, S.left) from
      ((moduleOverFrameRestriction X i M e).hom.val.app (op S)).hom x) =
      (show Γ(X, S.left) from (e.hom.val.app (op ((Over.map i).obj S))).hom x) := rfl

/-- Restricting the actual tensor frame is tensoring the originally restricted factor frames. -/
theorem moduleTensorOverUnitIso_restriction {U W : X.Opens} (i : W ⟶ U) (M N : X.Modules)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    moduleOverFrameRestriction X i (moduleTensor X M N) (moduleTensorOverUnitIso X M N U eM eN) =
      moduleTensorOverUnitIso X M N W (moduleOverFrameRestriction X i M eM)
        (moduleOverFrameRestriction X i N eN) := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  ext S : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨t, rfl⟩ := (moduleTensorSectionEquivOfFrames X M N W
    (moduleOverFrameRestriction X i M eM) (moduleOverFrameRestriction X i N eN) S.unop).surjective z
  rw [moduleTensorSectionEquivOfFrames_eq]
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
      change (show Γ(X, S.unop.left) from
        ((moduleOverFrameRestriction X i (moduleTensor X M N)
          (moduleTensorOverUnitIso X M N U eM eN)).hom.val.app S).hom
            (moduleTensorPureSection X M N S.unop.left x y)) = _
      exact (moduleOverFrameRestriction_apply X i (moduleTensor X M N)
        (moduleTensorOverUnitIso X M N U eM eN) S.unop
          (moduleTensorPureSection X M N S.unop.left x y)).trans
        ((moduleTensorOverUnitIso_pure X M N U eM eN ((Over.map i).obj S.unop) x y).trans
          (moduleTensorOverUnitIso_pure X M N W (moduleOverFrameRestriction X i M eM)
            (moduleOverFrameRestriction X i N eN) S.unop x y).symm)
  | add x y hx hy => simpa only [map_add] using congrArg₂ (fun a b : Γ(X, S.unop.left) => a+b) hx hy

/-- Native restriction by the identity preserves the original frame. -/
theorem moduleOverFrameRestriction_id (U : X.Opens) (M : X.Modules)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    moduleOverFrameRestriction X (𝟙 U) M e = e := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  ext S : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Successive native open restrictions equal restriction by the original composite inclusion. -/
theorem moduleOverFrameRestriction_comp {U W K : X.Opens} (i : W ⟶ U) (j : K ⟶ W)
    (M : X.Modules) (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    moduleOverFrameRestriction X j M (moduleOverFrameRestriction X i M e) =
      moduleOverFrameRestriction X (j ≫ i) M e := by
  apply Iso.ext
  apply SheafOfModules.hom_ext
  ext S : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- The original finite actual tensor frames commute with native restriction, including empty families. -/
theorem moduleTensorFamilyOverUnitIso_restriction {U W : X.Opens} (i : W ⟶ U) (n : ℕ) :
    ∀ (M : Fin n → X.Modules)
      (e : ∀ j, (M j).over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)),
    moduleOverFrameRestriction X i (moduleTensorFamily X n M) (moduleTensorFamilyOverUnitIso X U n M e) =
      moduleTensorFamilyOverUnitIso X W n M (fun j => moduleOverFrameRestriction X i (M j) (e j)) := by
  induction n with
  | zero =>
      intro M e
      apply Iso.ext
      apply SheafOfModules.hom_ext
      ext S : 1
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
  | succ n ih =>
      intro M e
      exact (moduleTensorOverUnitIso_restriction X i (M 0) (moduleTensorFamily X n (fun j => M j.succ))
        (e 0) (moduleTensorFamilyOverUnitIso X U n (fun j => M j.succ) (fun j => e j.succ))).trans
          (congrArg (fun d => moduleTensorOverUnitIso X (M 0) (moduleTensorFamily X n (fun j => M j.succ)) W
            (moduleOverFrameRestriction X i (M 0) (e 0)) d)
              (ih (fun j => M j.succ) (fun j => e j.succ)))

end BPFixedPoints.SheafTools
