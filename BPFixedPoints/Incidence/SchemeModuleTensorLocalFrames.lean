import BPFixedPoints.Incidence.SchemeModuleSheafificationOver
import BPFixedPoints.Incidence.SchemeModuleFiniteTensor
import BPFixedPoints.Incidence.TwoOpenTwistLocallyFree
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal

/-! # Original rank-one frames of actual tensor sheaves

The native presheaf tensor is already a sheaf on a common trivializing
open. The actual tensor frame retains the original pure-section product.
No global tensor coherence or derived product comparison is assumed.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (X : Scheme.{0})

/-- The original over-site module, retaining its commutative structure rings. -/
noncomputable abbrev moduleCommPresheafOver (M : X.Modules) (U : X.Opens) :
    PresheafOfModulesOfCommRing.{0} ((Over.forget U).op ⋙ X.presheaf) := (M.over U).val

/-- The native pointwise tensor commutes with restriction to the over-site. -/
noncomputable def moduleTensorPresheafOverIso (M N : X.Modules) (U : X.Opens) :
    (show PresheafOfModulesOfCommRing.{0} ((Over.forget U).op ⋙ X.presheaf) from
      (modulePresheafOverFunctor X U).obj (moduleTensorPresheaf X M N)) ≅
      (moduleCommPresheafOver X M U ⊗ moduleCommPresheafOver X N U) :=
  (Functor.Monoidal.μIso (PresheafOfModules.pushforward₀OfCommRingCat (Over.forget U) X.presheaf)
    (moduleCommPresheaf X M) (moduleCommPresheaf X N)).symm

/-- The specified original local frames trivialize the restricted presheaf tensor. -/
noncomputable def moduleTensorPresheafOverUnitIso (M N : X.Modules) (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (modulePresheafOverFunctor X U).obj (moduleTensorPresheaf X M N) ≅
      (SheafOfModules.unit (X.ringCatSheaf.over U)).val :=
  moduleTensorPresheafOverIso X M N U ≪≫
    tensorIso (C := PresheafOfModulesOfCommRing.{0} ((Over.forget U).op ⋙ X.presheaf))
      ((SheafOfModules.forget _).mapIso eM) ((SheafOfModules.forget _).mapIso eN) ≪≫
    λ_ (show PresheafOfModulesOfCommRing.{0} ((Over.forget U).op ⋙ X.presheaf) from
      (SheafOfModules.unit (X.ringCatSheaf.over U)).val)

/-- On a common rank-one chart the original tensor presheaf is already a sheaf. -/
theorem moduleTensorPresheafOver_isSheaf (M N : X.Modules) (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Presheaf.IsSheaf ((Opens.grothendieckTopology X).over U)
      ((modulePresheafOverFunctor X U).obj (moduleTensorPresheaf X M N)).presheaf :=
  (Presheaf.isSheaf_of_iso_iff ((PresheafOfModules.toPresheaf _).mapIso
    (moduleTensorPresheafOverUnitIso X M N U eM eN))).mpr
      (SheafOfModules.unit (X.ringCatSheaf.over U)).isSheaf

/-- The actual tensor sheaf has the specified rank-one frame over the native over-site. -/
noncomputable def moduleTensorOverUnitIso (M N : X.Modules) (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (moduleTensor X M N).over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  moduleSheafificationOverIso X _ U (moduleTensorPresheafOver_isSheaf X M N U eM eN) ≪≫
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (moduleTensorPresheafOverUnitIso X M N U eM eN)

/-- The actual tensor frame sends each original pure section to the product of its factor coefficients. -/
theorem moduleTensorOverUnitIso_pure (M N : X.Modules) (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (S : Over U) (x : Γ(M, S.left)) (y : Γ(N, S.left)) :
    ((moduleTensorOverUnitIso X M N U eM eN).hom.val.app (Opposite.op S)).hom
      (moduleTensorPureSection X M N S.left x y) =
        (show Γ(X, S.left) from (eM.hom.val.app (Opposite.op S)).hom x) *
          (show Γ(X, S.left) from (eN.hom.val.app (Opposite.op S)).hom y) := by
  have h := moduleSheafificationOverIso_unit X (moduleTensorPresheaf X M N) U
    (moduleTensorPresheafOver_isSheaf X M N U eM eN)
  have hv := congrArg (fun k => (k.app (Opposite.op S)).hom (x ⊗ₜ[Γ(X, S.left)] y)) h
  change ((moduleSheafificationOverIso X (moduleTensorPresheaf X M N) U
    (moduleTensorPresheafOver_isSheaf X M N U eM eN)).hom.val.app (Opposite.op S)).hom
      (moduleTensorPureSection X M N S.left x y) = x ⊗ₜ[Γ(X, S.left)] y at hv
  change ((moduleTensorPresheafOverUnitIso X M N U eM eN).hom.app (Opposite.op S)).hom
    (((moduleSheafificationOverIso X (moduleTensorPresheaf X M N) U
      (moduleTensorPresheafOver_isSheaf X M N U eM eN)).hom.val.app (Opposite.op S)).hom
        (moduleTensorPureSection X M N S.left x y)) = _
  rw [hv]
  rfl

/-- Actual geometric rank-one frames induce a rank-one frame for the actual tensor sheaf. -/
noncomputable def moduleTensorLocalUnitIso (M N : X.Modules) (U : X.Opens)
    (eM : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (eN : N.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (moduleTensor X M N).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (Scheme.Modules.overFunctorEquiv U).symm.app _ ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso
      (moduleTensorOverUnitIso X M N U (moduleOverUnitIso X M U eM) (moduleOverUnitIso X N U eN)) ≪≫
    U.sheafOfModulesEquivOverUnit X.ringCatSheaf

/-- The native over-site restriction of the original structure module is the original restricted structure module. -/
noncomputable def moduleUnitOverIso (U : X.Opens) :
    (SheafOfModules.unit X.ringCatSheaf).over U ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) := Iso.refl _

/-- Original over-site factor frames give finite actual tensor frames, including the empty family. -/
noncomputable def moduleTensorFamilyOverUnitIso (U : X.Opens) : (n : ℕ) →
    (M : Fin n → X.Modules) →
    (∀ i, (M i).over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) →
    ((moduleTensorFamily X n M).over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
  | 0, _, _ => moduleUnitOverIso X U
  | n+1, M, e => moduleTensorOverUnitIso X _ _ U (e 0)
      (moduleTensorFamilyOverUnitIso U n (fun i => M i.succ) (fun i => e i.succ))


/-- A common original rank-one chart trivializes every finite actual tensor, including the empty tensor. -/
noncomputable def moduleTensorFamilyLocalUnitIso (U : X.Opens) (n : ℕ) (M : Fin n → X.Modules)
    (e : ∀ i, (M i).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    (moduleTensorFamily X n M).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (Scheme.Modules.overFunctorEquiv U).symm.app _ ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso
      (moduleTensorFamilyOverUnitIso X U n M (fun i => moduleOverUnitIso X (M i) U (e i))) ≪≫
    U.sheafOfModulesEquivOverUnit X.ringCatSheaf

end BPFixedPoints.SheafTools
