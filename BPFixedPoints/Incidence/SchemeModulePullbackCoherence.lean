import BPFixedPoints.Incidence.SchemeModulePullbackTransitions

/-! # Native pullback composition and original rank-one frames

All comparisons use the original scheme modules and Mathlib functors.
The coefficient face atlas and derived-cohomology comparisons are separate.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable {X Y Z : Scheme.{0}}

/-- The native composition comparison retains the original pullback-pushforward hom-equivalence. -/
theorem modulePullbackComp_homEquiv (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (N : X.Modules)
    (k : (Scheme.Modules.pullback (f ≫ g)).obj M ⟶ N) :
    (((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv _ _)
        ((Scheme.Modules.pullbackComp f g).hom.app M ≫ k) =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _ k ≫
        (Scheme.Modules.pushforwardComp f g).inv.app N := by
  let A := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let B := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let α := (Scheme.Modules.pullbackComp f g).inv
  let β := (Scheme.Modules.pushforwardComp f g).hom
  have h := unit_conjugateEquiv A B α M
  have hc : conjugateEquiv A B α = β := Scheme.Modules.conjugateEquiv_pullbackComp_inv f g
  rw [hc] at h
  apply (cancel_mono ((Scheme.Modules.pushforwardComp f g).hom.app N)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rw [Category.assoc, β.naturality, ← Category.assoc, h]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp]
  simp only [α, Iso.inv_hom_id_app_assoc]
  rfl

/-- The native structure-module frames agree for successive and composite pullbacks. -/
theorem modulePullbackUnitIso_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).hom.app (SheafOfModules.unit Z.ringCatSheaf) ≫
      (modulePullbackUnitIso (f ≫ g)).hom =
        (Scheme.Modules.pullback f).map (modulePullbackUnitIso g).hom ≫ (modulePullbackUnitIso f).hom := by
  let A := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let uX := SheafOfModules.unit X.ringCatSheaf
  let uZ := SheafOfModules.unit Z.ringCatSheaf
  have hf : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      ((Scheme.Modules.pullback f).map (modulePullbackUnitIso g).hom ≫ (modulePullbackUnitIso f).hom) =
      (modulePullbackUnitIso g).hom ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left
      (modulePullbackUnitIso g).hom (modulePullbackUnitIso f).hom).trans
        (congrArg (fun k => (modulePullbackUnitIso g).hom ≫ k) (modulePullbackUnitIso_adjunction f))
  have hg : (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      ((modulePullbackUnitIso g).hom ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward g).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_naturality_right
      (modulePullbackUnitIso g).hom (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).trans
        (congrArg (fun k => k ≫ (Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) (modulePullbackUnitIso_adjunction g))
  have hR : A.homEquiv uZ uX
      ((Scheme.Modules.pullback f).map (modulePullbackUnitIso g).hom ≫ (modulePullbackUnitIso f).hom) =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward g).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) := by
    rw [show A = (Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f) from rfl, Adjunction.comp_homEquiv]
    change (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ _) = _
    exact (congrArg (fun k => (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _ k) hf).trans hg
  apply (A.homEquiv _ _).injective
  refine (modulePullbackComp_homEquiv f g uZ uX (modulePullbackUnitIso (f ≫ g)).hom).trans ?_
  refine (congrArg (fun k => k ≫ (Scheme.Modules.pushforwardComp f g).inv.app uX)
    (modulePullbackUnitIso_adjunction (f ≫ g))).trans ?_
  refine Eq.trans ?_ hR.symm
  apply (cancel_mono ((Scheme.Modules.pushforwardComp f g).hom.app uX)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- On an open immersion the canonical pullback frame is the original geometric restriction-unit frame. -/
theorem modulePullbackUnitIso_open (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctorIsoPullback f).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
      (modulePullbackUnitIso f).hom = (Scheme.Modules.restrictUnitIso f).hom := by
  let A := Scheme.Modules.restrictAdjunction f
  let B := Scheme.Modules.pullbackPushforwardAdjunction f
  apply (A.homEquiv _ _).injective
  have hL : A.homEquiv _ _
      ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app (SheafOfModules.unit Y.ringCatSheaf) ≫
        (modulePullbackUnitIso f).hom) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
    change A.homEquiv _ _ ((A.leftAdjointUniq B).hom.app _ ≫ (modulePullbackUnitIso f).hom) = _
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
    exact modulePullbackUnitIso_adjunction f
  rw [hL]
  symm
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Γ(Y, U.unop) at x
  change (f.appIso (f ⁻¹ᵁ U.unop)).hom
    (Y.presheaf.map (homOfLE (f.image_preimage_le U.unop)).op x) = (f.app U.unop).hom x
  have h := congrArg (fun k => k ≫ (f.appIso (f ⁻¹ᵁ U.unop)).hom) (f.app_appIso_inv U.unop)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  exact congrArg (fun k => k.hom x) h.symm

variable {W : Scheme.{0}}

/-- The native comparison for equal scheme maps is the original equality-induced functor morphism. -/
theorem modulePullbackCongr_hom {f g : X ⟶ Y} (h : f = g) :
    (Scheme.Modules.pullbackCongr h).hom = eqToHom (congrArg Scheme.Modules.pullback h) := by
  cases h
  rfl

/-- The native three-map composition comparison retains the original scheme-map associativity. -/
theorem modulePullbackComp_associativity (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (Scheme.Modules.pullbackComp h (f ≫ g)).inv.app M ≫
      (Scheme.Modules.pullback h).map ((Scheme.Modules.pullbackComp f g).inv.app M) ≫
        (Scheme.Modules.pullbackComp h f).hom.app ((Scheme.Modules.pullback g).obj M) =
      (Scheme.Modules.pullbackCongr (Category.assoc h f g).symm).hom.app M ≫
        (Scheme.Modules.pullbackComp (h ≫ f) g).inv.app M := by
  apply (cancel_mono ((Scheme.Modules.pullbackComp (h ≫ f) g).hom.app M)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have hc := congrArg (fun t => t.app M) (Scheme.Modules.pseudofunctor_associativity h f g)
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id, modulePullbackCongr_hom] using hc

/-- Pull back the specified original rank-one frame using native composition and the canonical structure-module frame. -/
noncomputable def modulePullbackFrame (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (e : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback (f ≫ g)).obj M ≅ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.pullbackComp f g).symm.app M ≪≫
    (Scheme.Modules.pullback f).mapIso e ≪≫ modulePullbackUnitIso f

/-- The specified rank-one frame has the same pullback under successive and composite scheme maps. -/
theorem modulePullbackFrame_comp (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (e : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit Y.ringCatSheaf) :
    modulePullbackFrame h (f ≫ g) M (modulePullbackFrame f g M e) =
      (Scheme.Modules.pullbackCongr (Category.assoc h f g).symm).app M ≪≫
        modulePullbackFrame (h ≫ f) g M e := by
  apply Iso.ext
  have hn := (Scheme.Modules.pullbackComp h f).hom.naturality e.hom
  change (Scheme.Modules.pullback h).map ((Scheme.Modules.pullback f).map e.hom) ≫
    (Scheme.Modules.pullbackComp h f).hom.app (SheafOfModules.unit Y.ringCatSheaf) =
      (Scheme.Modules.pullbackComp h f).hom.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullback (h ≫ f)).map e.hom at hn
  have ht := congrArg (fun k => k ≫ (modulePullbackUnitIso (h ≫ f)).hom) hn
  simp only [Category.assoc] at ht
  dsimp only [modulePullbackFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← modulePullbackUnitIso_comp h f, ht]
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ (Scheme.Modules.pullback (h ≫ f)).map e.hom ≫ (modulePullbackUnitIso (h ≫ f)).hom)
      (modulePullbackComp_associativity h f g M)

end BPFixedPoints.SheafTools
