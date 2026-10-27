import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Pulling back the original rank-one local frames

The structure-module comparison is Mathlib's canonical pullback map.
The local comparison uses native pullback composition and open restriction.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable {X Y : Scheme.{0}}

/-- The canonical native pullback of the original structure module is the structure module. -/
noncomputable def modulePullbackUnitIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI : (TopologicalSpace.Opens.map f.base).Final := inferInstance
  letI : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    inferInstanceAs (IsIso (SheafOfModules.pullbackObjUnitToUnit
      (F := TopologicalSpace.Opens.map f.base) f.toRingCatSheafHom))
  exact asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)

/-- Pull back the specified original local frame along its actual geometric factorization. -/
noncomputable def modulePullbackLocalUnitIso (f : X ⟶ Y) (U : Y.Opens)
    (M : Y.Modules) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (g : X ⟶ U) (hg : g ≫ U.ι = f) :
    (Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.pullbackCongr hg.symm).app M ≪≫
    (Scheme.Modules.pullbackComp g U.ι).symm.app M ≪≫
    (Scheme.Modules.pullback g).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e) ≪≫
    modulePullbackUnitIso g

/-- The canonical unit comparison is adjoint to the original map of structure sheaves. -/
theorem modulePullbackUnitIso_adjunction (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (modulePullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
  SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

end BPFixedPoints.SheafTools
