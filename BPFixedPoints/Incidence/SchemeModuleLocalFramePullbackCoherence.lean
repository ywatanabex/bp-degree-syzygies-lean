import BPFixedPoints.Incidence.SchemeModuleRestrictionPullbackCoherence
import BPFixedPoints.Incidence.SchemeModuleFrameGeometricComparison
/-! # Pullback of the specified original local frames -/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable {X Y W : Scheme.{0}}
/-- Pulling back the original local frame preserves its actual factorization. -/
theorem modulePullbackLocalUnitIso_comp (h : W ⟶ X) (f : X ⟶ Y) (U : Y.Opens) (M : Y.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (g : X ⟶ U) (hg : g ≫ U.ι = f) :
    modulePullbackFrame h f M (modulePullbackLocalUnitIso f U M e g hg) =
      modulePullbackLocalUnitIso (h ≫ f) U M e (h ≫ g) (by rw [Category.assoc, hg]) := by
  subst f
  apply Iso.ext
  have hc := congrArg Iso.hom (modulePullbackFrame_comp h g U.ι M
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e))
  simpa only [modulePullbackLocalUnitIso, modulePullbackFrame,
    Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Functor.mapIso_hom, Functor.map_comp, CategoryTheory.Functor.map_id, Category.assoc] using hc
variable {Z : Scheme.{0}}

/-- Geometric restriction of an original frame is its canonical pullback frame on a composite open. -/
theorem moduleCompositeOpenFrame_eq_pullback (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (M : Z.Modules)
    (e : M.restrict g ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.restrictFunctorComp f g).hom.app M ≫
      (Scheme.Modules.restrictFunctor f).map e.hom ≫
      (Scheme.Modules.restrictUnitIso f).hom =
    (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom.app M ≫
      (modulePullbackFrame f g M
        ((Scheme.Modules.restrictFunctorIsoPullback g).symm.app M ≪≫ e)).hom := by
  rw [← moduleRestrictionPullback_comp f g M]
  simp only [modulePullbackFrame, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [Iso.hom_inv_id_app_assoc]
  have hn := (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality
    ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app M ≫ e.hom)
  simp only [Functor.map_comp, Category.assoc] at hn
  have hnp := congrArg (fun k => k ≫ (modulePullbackUnitIso f).hom) hn
  simp only [Category.assoc] at hnp ⊢
  rw [← hnp, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [modulePullbackUnitIso_open]

/-- The native restriction-to-pullback comparison respects equality of the original open maps. -/
theorem moduleRestrictionPullback_congr {f g : X ⟶ Y}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) (M : Y.Modules) :
    (Scheme.Modules.restrictFunctorCongr h).hom.app M ≫
      (Scheme.Modules.restrictFunctorIsoPullback g).hom.app M =
    (Scheme.Modules.restrictFunctorIsoPullback f).hom.app M ≫
      (Scheme.Modules.pullbackCongr h).hom.app M := by
  subst g
  have hc : (Scheme.Modules.restrictFunctorCongr (rfl : f = f)).hom.app M = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro S
    ext x
    simp only [Scheme.Modules.restrictFunctorCongr_hom_app_app, eqToHom_refl, op_id,
      CategoryTheory.Functor.map_id]
    rfl
  rw [hc]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp, Category.comp_id]

/-- The original local frame restriction is the canonical pullback along the original open inclusion. -/
theorem moduleLocalFrameRestriction_eq_pullback (T : Scheme.{0}) {U S : T.Opens}
    (i : S ⟶ U) (M : T.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    moduleLocalFrameRestriction T i M e =
      (Scheme.Modules.restrictFunctorIsoPullback S.ι).app M ≪≫
        modulePullbackLocalUnitIso S.ι U M e (T.homOfLE (leOfHom i))
          (T.homOfLE_ι (leOfHom i)) := by
  rw [moduleLocalFrameRestriction_eq_geometric]
  apply Iso.ext
  simp only [moduleGeometricFrameRestriction, moduleRestrictionCompIso,
    modulePullbackLocalUnitIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  have hc := moduleCompositeOpenFrame_eq_pullback (T.homOfLE (leOfHom i)) U.ι M e
  simp only [modulePullbackFrame, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom] at hc
  rw [hc]
  have hn := moduleRestrictionPullback_congr (T.homOfLE_ι (leOfHom i)).symm M
  simpa only [Category.assoc] using congrArg (fun k => k ≫
    (Scheme.Modules.pullbackComp (T.homOfLE (leOfHom i)) U.ι).inv.app M ≫
      (Scheme.Modules.pullback (T.homOfLE (leOfHom i))).map
        ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M ≫ e.hom) ≫
          (modulePullbackUnitIso (T.homOfLE (leOfHom i))).hom) hn

/-- Refining the original trivializing open preserves the specified pullback frame. -/
theorem modulePullbackLocalUnitIso_refine {T : Scheme.{0}} {U S : T.Opens} (i : S ⟶ U) (M : T.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (k : X ⟶ S) :
    modulePullbackLocalUnitIso (k ≫ S.ι) U M e (k ≫ T.homOfLE (leOfHom i))
      (by rw [Category.assoc, T.homOfLE_ι]) =
    modulePullbackLocalUnitIso (k ≫ S.ι) S M (moduleLocalFrameRestriction T i M e) k rfl := by
  rw [moduleLocalFrameRestriction_eq_pullback]
  have hc := modulePullbackLocalUnitIso_comp k S.ι U M e
    (T.homOfLE (leOfHom i)) (T.homOfLE_ι (leOfHom i))
  apply Iso.ext
  have hch := congrArg Iso.hom hc.symm
  simp only [modulePullbackFrame, modulePullbackLocalUnitIso, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_app, Category.id_comp,
    Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app] at hch ⊢
  have hz {N : X.Modules}
      (q : (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback S.ι).obj M) ⟶ N) :
      (Scheme.Modules.pullback k).map ((Scheme.Modules.restrictFunctorIsoPullback S.ι).inv.app M) ≫
        (Scheme.Modules.pullback k).map ((Scheme.Modules.restrictFunctorIsoPullback S.ι).hom.app M) ≫ q = q := by
    rw [← Category.assoc, ← (Scheme.Modules.pullback k).map_comp,
      Iso.inv_hom_id_app, (Scheme.Modules.pullback k).map_id, Category.id_comp]
  rw [hz]
  exact hch

/-- Refining the original trivializing open preserves the frame along the specified actual lifts. -/
theorem modulePullbackLocalUnitIso_refine_fac {T : Scheme.{0}} {U S : T.Opens}
    (i : S ⟶ U) (M : T.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (f : X ⟶ T) (g : X ⟶ U) (hg : g ≫ U.ι = f)
    (k : X ⟶ S) (hk : k ≫ S.ι = f) (hkg : k ≫ T.homOfLE (leOfHom i) = g) :
    modulePullbackLocalUnitIso f U M e g hg =
      modulePullbackLocalUnitIso f S M (moduleLocalFrameRestriction T i M e) k hk := by
  cases hk
  cases hkg
  exact modulePullbackLocalUnitIso_refine i M e k

end BPFixedPoints.SheafTools
