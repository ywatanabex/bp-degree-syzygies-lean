import BPFixedPoints.Incidence.SchemeModuleLocalFramePullbackCoherence

/-! # Original pullback frames and ambient open restriction

The right-hand scheme morphism is arbitrary. Only the actual open inclusions
are treated as open immersions. All comparison maps are Mathlib's native maps.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable {W X Y Z : Scheme.{0}}

/-- Reversing the equality of the original maps reverses their native pullback comparison. -/
theorem modulePullbackCongr_reverse {f g : X ⟶ Y} (h : f = g) :
    Scheme.Modules.pullbackCongr h.symm = (Scheme.Modules.pullbackCongr h).symm := by
  cases h
  rfl

/-- The native pullback comparisons preserve composition of equalities of the original maps. -/
theorem modulePullbackCongr_trans {f g h : X ⟶ Y} (p : f = g) (q : g = h) (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr p).app M ≪≫ (Scheme.Modules.pullbackCongr q).app M =
      (Scheme.Modules.pullbackCongr (p.trans q)).app M := by
  cases p
  cases q
  apply Iso.ext
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_hom,
    Iso.app_hom, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

/-- Native pullback composition respects equality in its original left scheme morphism. -/
theorem modulePullbackComp_congr_left {f g : X ⟶ Y} (h : f = g) (k : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullbackCongr h).app ((Scheme.Modules.pullback k).obj M) ≪≫
      (Scheme.Modules.pullbackComp g k).app M =
    (Scheme.Modules.pullbackComp f k).app M ≪≫
      (Scheme.Modules.pullbackCongr (congrArg (fun z => z ≫ k) h)).app M := by
  cases h
  apply Iso.ext
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_hom,
    Iso.app_hom, Iso.refl_hom, NatTrans.id_app, Category.id_comp, Category.comp_id]

/-- Pulling back an original frame respects the additional original right factor. -/
theorem modulePullbackFrame_whisker (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules)
    (e : (Scheme.Modules.pullback (f ≫ g)).obj M ≅ SheafOfModules.unit X.ringCatSheaf) :
    modulePullbackFrame h f ((Scheme.Modules.pullback g).obj M)
      ((Scheme.Modules.pullbackComp f g).app M ≪≫ e) =
    (Scheme.Modules.pullbackComp (h ≫ f) g).app M ≪≫
      (Scheme.Modules.pullbackCongr (Category.assoc h f g)).app M ≪≫
        modulePullbackFrame h (f ≫ g) M e := by
  apply Iso.ext
  have hc := modulePullbackComp_associativity h f g M
  rw [modulePullbackCongr_reverse (Category.assoc h f g)] at hc
  apply (cancel_epi ((Scheme.Modules.pullbackComp h f).hom.app
    ((Scheme.Modules.pullback g).obj M))).mp
  simp only [modulePullbackFrame, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  apply (cancel_epi ((Scheme.Modules.pullback h).map
    ((Scheme.Modules.pullbackComp f g).inv.app M))).mp
  simp only [← Functor.map_comp_assoc]
  have hcp := congrArg (fun k => (Scheme.Modules.pullbackComp h (f ≫ g)).hom.app M ≫ k ≫
    (Scheme.Modules.pullbackComp (h ≫ f) g).hom.app M ≫
      (Scheme.Modules.pullbackCongr (Category.assoc h f g)).hom.app M ≫
        (Scheme.Modules.pullbackComp h (f ≫ g)).inv.app M ≫
          (Scheme.Modules.pullback h).map e.hom ≫ (modulePullbackUnitIso h).hom) hc
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc,
    Iso.symm_hom] using hcp.symm

/-- Changing only the original ambient map preserves a specified local pullback frame. -/
theorem modulePullbackLocalUnitIso_source_congr {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (M : Y.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (k : X ⟶ U) (hf : k ≫ U.ι = f) (hg : k ≫ U.ι = g) :
    (Scheme.Modules.pullbackCongr h).app M ≪≫ modulePullbackLocalUnitIso g U M e k hg =
      modulePullbackLocalUnitIso f U M e k hf := by
  cases h
  apply Iso.ext
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_hom,
    Iso.app_hom, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

/-- Ambient restriction of the original pullback chart frame retains native composition with an arbitrary map. -/
theorem moduleLocalFrameRestriction_pullbackChart (T : Scheme.{0}) {U S : T.Opens}
    (i : S ⟶ U) (f : T ⟶ Y) (M : Y.Modules)
    (e : (Scheme.Modules.pullback (U.ι ≫ f)).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    moduleLocalFrameRestriction T i ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
        (Scheme.Modules.pullbackComp U.ι f).app M ≪≫ e) =
    (Scheme.Modules.restrictFunctorIsoPullback S.ι).app _ ≪≫
      (Scheme.Modules.pullbackComp S.ι f).app M ≪≫
      (Scheme.Modules.pullbackCongr
        (show S.ι ≫ f = T.homOfLE (leOfHom i) ≫ U.ι ≫ f by
          rw [← Category.assoc, T.homOfLE_ι])).app M ≪≫
        modulePullbackFrame (T.homOfLE (leOfHom i)) (U.ι ≫ f) M e := by
  let t := T.homOfLE (leOfHom i)
  let N := (Scheme.Modules.pullback f).obj M
  have hfirst : modulePullbackLocalUnitIso S.ι U N
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N ≪≫
        (Scheme.Modules.pullbackComp U.ι f).app M ≪≫ e) t (T.homOfLE_ι (leOfHom i)) =
      (Scheme.Modules.pullbackCongr (T.homOfLE_ι (leOfHom i)).symm).app N ≪≫
        modulePullbackFrame t U.ι N ((Scheme.Modules.pullbackComp U.ι f).app M ≪≫ e) := by
    apply Iso.ext
    simp only [modulePullbackLocalUnitIso, modulePullbackFrame, Iso.trans_hom,
      Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    have hz {P : S.toScheme.Modules}
        (q : (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback U.ι).obj N) ⟶ P) :
        (Scheme.Modules.pullback t).map ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app N) ≫
          (Scheme.Modules.pullback t).map ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app N) ≫ q = q := by
      rw [← Category.assoc, ← (Scheme.Modules.pullback t).map_comp,
        Iso.inv_hom_id_app, (Scheme.Modules.pullback t).map_id, Category.id_comp]
    rw [hz]
  rw [moduleLocalFrameRestriction_eq_pullback, hfirst, modulePullbackFrame_whisker]
  have hd := modulePullbackComp_congr_left (T.homOfLE_ι (leOfHom i)).symm f M
  have hdp := congrArg (fun z => (Scheme.Modules.restrictFunctorIsoPullback S.ι).app N ≪≫ z ≪≫
    (Scheme.Modules.pullbackCongr (Category.assoc t U.ι f)).app M ≪≫
      modulePullbackFrame t (U.ι ≫ f) M e) hd
  simp only [Iso.trans_assoc] at hdp ⊢
  rw [hdp]
  have he := modulePullbackCongr_trans
    (congrArg (fun z => z ≫ f) (T.homOfLE_ι (leOfHom i)).symm)
    (Category.assoc t U.ι f) M
  have hep := congrArg (fun z => (Scheme.Modules.restrictFunctorIsoPullback S.ι).app N ≪≫
    (Scheme.Modules.pullbackComp S.ι f).app M ≪≫ z ≪≫
      modulePullbackFrame t (U.ι ≫ f) M e) he
  simpa only [Iso.trans_assoc] using hep

/-- Ambient restriction of an original local pullback frame follows its original restricted lift. -/
theorem moduleLocalFrameRestriction_pullbackLocalFrame (T : Scheme.{0}) {U S : T.Opens}
    (i : S ⟶ U) (f : T ⟶ Y) (A : Y.Opens) (M : Y.Modules)
    (e : M.restrict A.ι ≅ SheafOfModules.unit A.toScheme.ringCatSheaf)
    (g : U.toScheme ⟶ A) (hg : g ≫ A.ι = U.ι ≫ f) :
    moduleLocalFrameRestriction T i ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
        (Scheme.Modules.pullbackComp U.ι f).app M ≪≫
          modulePullbackLocalUnitIso (U.ι ≫ f) A M e g hg) =
    (Scheme.Modules.restrictFunctorIsoPullback S.ι).app _ ≪≫
      (Scheme.Modules.pullbackComp S.ι f).app M ≪≫
        modulePullbackLocalUnitIso (S.ι ≫ f) A M e (T.homOfLE (leOfHom i) ≫ g)
          (by rw [Category.assoc, hg, ← Category.assoc, T.homOfLE_ι]) := by
  have hm := moduleLocalFrameRestriction_pullbackChart T i f M
    (modulePullbackLocalUnitIso (U.ι ≫ f) A M e g hg)
  rw [modulePullbackLocalUnitIso_comp] at hm
  have hc := modulePullbackLocalUnitIso_source_congr
    (show S.ι ≫ f = T.homOfLE (leOfHom i) ≫ U.ι ≫ f by
      rw [← Category.assoc, T.homOfLE_ι]) A M e (T.homOfLE (leOfHom i) ≫ g)
    (by rw [Category.assoc, hg, ← Category.assoc, T.homOfLE_ι])
    (by rw [Category.assoc, hg])
  refine hm.trans ?_
  simpa only [Iso.trans_assoc] using congrArg (fun z =>
    (Scheme.Modules.restrictFunctorIsoPullback S.ι).app ((Scheme.Modules.pullback f).obj M) ≪≫
      (Scheme.Modules.pullbackComp S.ι f).app M ≪≫ z) hc

end BPFixedPoints.SheafTools
