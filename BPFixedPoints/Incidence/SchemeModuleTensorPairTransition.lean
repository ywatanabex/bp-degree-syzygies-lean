import BPFixedPoints.Incidence.SchemeModuleFrameGluing

/-! # The original binary tensor frame has the product transition

The original arbitrary-section tensor transition formula is packaged as
an equality of the same original over-site sheaf morphisms.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1300000
variable (X : Scheme.{0}) (M N : X.Modules) (U : X.Opens)

/-- The original actual tensor frame multiplies the same original geometric factor transitions. -/
theorem moduleTensorOverFrame_transition
    (eM fM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN fN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r s : Γ(U.toScheme,⊤))
    (hM : eM.hom = fM.hom ≫ moduleOverMultiplication X U r)
    (hN : eN.hom = fN.hom ≫ moduleOverMultiplication X U s) :
    (moduleTensorOverUnitIso X M N U eM eN).hom =
      (moduleTensorOverUnitIso X M N U fM fN).hom ≫ moduleOverMultiplication X U (r*s) := by
  apply SheafOfModules.hom_ext
  ext S : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change ((moduleTensorOverUnitIso X M N U eM eN).hom.val.app S).hom z =
    ((moduleOverMultiplication X U (r*s)).val.app S).hom
      (((moduleTensorOverUnitIso X M N U fM fN).hom.val.app S).hom z)
  have hm := moduleOverMultiplication_app X U (r*s) S.unop
    (((moduleTensorOverUnitIso X M N U fM fN).hom.val.app S).hom z)
  rw [moduleOverMultiplicationCoefficient_mul] at hm
  refine Eq.trans ?_ hm.symm
  apply moduleTensorOverUnitIso_change X M N U eM fM eN fN S.unop
    (moduleOverMultiplicationCoefficient X U r S.unop)
    (moduleOverMultiplicationCoefficient X U s S.unop)
  · intro x
    have h := congrArg (fun f => (f.val.app S).hom x) hM
    exact h.trans (moduleOverMultiplication_app X U r S.unop _)
  · intro x
    have h := congrArg (fun f => (f.val.app S).hom x) hN
    exact h.trans (moduleOverMultiplication_app X U s S.unop _)

end BPFixedPoints.SheafTools
