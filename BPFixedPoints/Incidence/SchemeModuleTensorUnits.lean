import BPFixedPoints.Incidence.SchemeModuleTensorSections

/-! # Original unit-section formulas for the actual sheaf tensor

The unit comparisons are the original presheaf unitors followed by the native
sheafification counit. Their section formulas follow from the original
adjunction triangle, not from a later coordinate comparison.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (X : Scheme.{0}) (M : X.Modules)

/-- The original sheafification unit followed by its actual counit recovers every original section. -/
theorem moduleSheafificationIso_unit_app (U : X.Opens) (x : Γ(M, U)) :
    (moduleSheafificationIso X M).hom.app U
      (((moduleSheafificationAdjunction X).unit.app (moduleCommPresheaf X M)).app (op U) x) = x := by
  have h := (moduleSheafificationAdjunction X).right_triangle_components M
  have hx := congrArg (fun k : moduleCommPresheaf X M ⟶ moduleCommPresheaf X M =>
    (k.app (op U)).hom x) h
  exact hx

/-- The actual left unit comparison sends the original pure section to the original scalar multiple. -/
theorem moduleTensorLeftUnitIso_pure (U : X.Opens) (r : Γ(X, U)) (x : Γ(M, U)) :
    (moduleTensorLeftUnitIso X M).hom.app U
      (moduleTensorPureSection X (SheafOfModules.unit X.ringCatSheaf) M U r x) = r • x := by
  let h : moduleTensorPresheaf X (SheafOfModules.unit X.ringCatSheaf) M ⟶ moduleCommPresheaf X M :=
    (λ_ (moduleCommPresheaf X M)).hom
  have hn := (moduleSheafificationAdjunction X).unit.naturality h
  have hx := congrArg (fun k : moduleTensorPresheaf X (SheafOfModules.unit X.ringCatSheaf) M ⟶
      moduleCommPresheaf X ((moduleSheafification X).obj (moduleCommPresheaf X M)) =>
        (moduleSheafificationIso X M).hom.app U ((k.app (op U)).hom (r ⊗ₜ[Γ(X, U)] x))) hn
  change (moduleSheafificationIso X M).hom.app U
      (((moduleSheafificationAdjunction X).unit.app (moduleCommPresheaf X M)).app (op U) (r • x)) =
    (moduleTensorLeftUnitIso X M).hom.app U
      (moduleTensorPureSection X (SheafOfModules.unit X.ringCatSheaf) M U r x) at hx
  exact hx.symm.trans (moduleSheafificationIso_unit_app X M U (r • x))

/-- The actual right unit comparison sends the original pure section to the original scalar multiple. -/
theorem moduleTensorRightUnitIso_pure (U : X.Opens) (x : Γ(M, U)) (r : Γ(X, U)) :
    (moduleTensorRightUnitIso X M).hom.app U
      (moduleTensorPureSection X M (SheafOfModules.unit X.ringCatSheaf) U x r) = r • x := by
  let h : moduleTensorPresheaf X M (SheafOfModules.unit X.ringCatSheaf) ⟶ moduleCommPresheaf X M :=
    (ρ_ (moduleCommPresheaf X M)).hom
  have hn := (moduleSheafificationAdjunction X).unit.naturality h
  have hx := congrArg (fun k : moduleTensorPresheaf X M (SheafOfModules.unit X.ringCatSheaf) ⟶
      moduleCommPresheaf X ((moduleSheafification X).obj (moduleCommPresheaf X M)) =>
        (moduleSheafificationIso X M).hom.app U ((k.app (op U)).hom (x ⊗ₜ[Γ(X, U)] r))) hn
  change (moduleSheafificationIso X M).hom.app U
      (((moduleSheafificationAdjunction X).unit.app (moduleCommPresheaf X M)).app (op U) (r • x)) =
    (moduleTensorRightUnitIso X M).hom.app U
      (moduleTensorPureSection X M (SheafOfModules.unit X.ringCatSheaf) U x r) at hx
  exact hx.symm.trans (moduleSheafificationIso_unit_app X M U (r • x))

end BPFixedPoints.SheafTools
