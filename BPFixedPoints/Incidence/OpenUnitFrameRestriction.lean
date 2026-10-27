import BPFixedPoints.Incidence.SchemeModuleFrameGeometricComparison
import BPFixedPoints.Incidence.TwoOpenTwistTransitions
/-! # Original open structure frames under native geometric restriction -/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (X : Scheme.{0})
/-- Restriction retains the original morphism components. -/
theorem moduleRestriction_map_app {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    {M N : X.Modules} (k : M ⟶ N) (S : Y.Opens) :
    ((Scheme.Modules.restrictFunctor f).map k).app S = k.app (f ''ᵁ S) := rfl
/-- The original restriction counit is the equality-induced presheaf restriction. -/
theorem moduleRestrictionCounit_app {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : Y.Modules) (S : Y.Opens) :
    ((Scheme.Modules.restrictFunctorAdjCounitIso f).hom.app M).app S =
      M.presheaf.map (eqToHom (f.preimage_image_eq S).symm).op := rfl
/-- The original open structure restriction commutes with the native counit and unit frames. -/
theorem openUnitFrameRestriction {U W : X.Opens} (h : W ≤ U) :
    (moduleRestrictionCompIso X (homOfLE h) (openUnitModule X U)).hom ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
        ((Scheme.Modules.restrictFunctorAdjCounitIso U.ι).hom.app
          (SheafOfModules.unit U.toScheme.ringCatSheaf)) ≫
      (Scheme.Modules.restrictUnitIso (X.homOfLE h)).hom =
    (Scheme.Modules.restrictFunctor W.ι).map (openUnitRestriction X h) ≫
      (Scheme.Modules.restrictFunctorAdjCounitIso W.ι).hom.app
        (SheafOfModules.unit W.toScheme.ringCatSheaf) := by
  apply Scheme.Modules.hom_ext
  intro S
  ext x
  simp only [moduleRestrictionCompIso, Iso.trans_hom, Iso.app_hom,
    Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app, moduleRestriction_map_app,
    moduleRestrictionCounit_app, AddCommGrpCat.comp_apply]
  simp only [openUnitRestriction, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Scheme.Modules.pushforward_map_app, AddCommGrpCat.comp_apply]
  change ((X.homOfLE h).appIso S).hom _ = _
  apply (ConcreteCategory.bijective_of_isIso ((X.homOfLE h).appIso S).inv).injective
  simp only [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  rw [Scheme.Hom.appIso_homOfLE_inv]
  change (X.presheaf.map _).hom ((X.presheaf.map _).hom ((X.presheaf.map _).hom x)) =
    (X.presheaf.map _).hom ((X.presheaf.map _).hom ((X.presheaf.map _).hom
      (((X.homOfLE h).app (U.ι ⁻¹ᵁ (W.ι ''ᵁ S))).hom x)))
  rw [Scheme.homOfLE_app]
  simp only [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  change (X.presheaf.map _).hom x =
    (X.presheaf.map _).hom ((X.presheaf.map _).hom x)
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  congr 2
/-- The native composite-restriction comparison is natural in the original module. -/
@[reassoc] theorem moduleRestrictionCompIso_naturality {U W : X.Opens} (i : W ⟶ U)
    {M N : X.Modules} (p : M ⟶ N) :
    (moduleRestrictionCompIso X i M).hom ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE (leOfHom i))).map
        ((Scheme.Modules.restrictFunctor U.ι).map p) =
    (Scheme.Modules.restrictFunctor W.ι).map p ≫
      (moduleRestrictionCompIso X i N).hom :=
  (((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι (leOfHom i)).symm) ≪≫
    Scheme.Modules.restrictFunctorComp (X.homOfLE (leOfHom i)) U.ι).hom.naturality p).symm

/-- Restricting the original projection frame agrees with the original smaller-open projection frame. -/
theorem openUnitProjectionFrameRestriction {U W : X.Opens} (h : W ≤ U)
    (M : X.Modules) (p : M ⟶ openUnitModule X U) :
    (moduleRestrictionCompIso X (homOfLE h) M).hom ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
        ((Scheme.Modules.restrictFunctor U.ι).map p ≫
          (Scheme.Modules.restrictFunctorAdjCounitIso U.ι).hom.app
            (SheafOfModules.unit U.toScheme.ringCatSheaf)) ≫
      (Scheme.Modules.restrictUnitIso (X.homOfLE h)).hom =
    (Scheme.Modules.restrictFunctor W.ι).map (p ≫ openUnitRestriction X h) ≫
      (Scheme.Modules.restrictFunctorAdjCounitIso W.ι).hom.app
        (SheafOfModules.unit W.toScheme.ringCatSheaf) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [moduleRestrictionCompIso_naturality_assoc, openUnitFrameRestriction]

/-- The original left overlap frame is the native restriction of the original left chart frame. -/
theorem twoOpenTwistLeftIso_restriction (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    moduleLocalFrameRestriction X (homOfLE inf_le_left)
      (twoOpenTwistModule X U V u) (twoOpenTwistLeftIso X U V u) =
        twoOpenTwistOverlapLeftIso X U V u := by
  rw [moduleLocalFrameRestriction_eq_geometric]
  apply Iso.ext
  exact openUnitProjectionFrameRestriction X inf_le_left _
    (twoOpenTwistInclusion X U V u ≫ biprod.fst)

/-- The original right overlap frame is the native restriction of the original right chart frame. -/
theorem twoOpenTwistRightIso_restriction (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    moduleLocalFrameRestriction X (homOfLE inf_le_right)
      (twoOpenTwistModule X U V u) (twoOpenTwistRightIso X U V u) =
        twoOpenTwistOverlapRightIso X U V u := by
  rw [moduleLocalFrameRestriction_eq_geometric]
  apply Iso.ext
  exact openUnitProjectionFrameRestriction X inf_le_right _
    (twoOpenTwistInclusion X U V u ≫ biprod.snd)

end BPFixedPoints.SheafTools
