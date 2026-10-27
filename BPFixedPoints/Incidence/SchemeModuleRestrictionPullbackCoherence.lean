import BPFixedPoints.Incidence.SchemeModulePullbackCoherence

/-! # Native open restriction and pullback composition

The comparisons use Mathlib's original restriction, pullback, pushforward and
adjunction maps. No replacement of a comparison isomorphism is made.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [IsOpenImmersion f] [IsOpenImmersion g]

/-- Native restriction retains the original presheaf restriction maps. -/
theorem moduleRestriction_presheaf_map (M : Y.Modules) {U V : X.Opens} (i : U ⟶ V) :
    (M.restrict f).presheaf.map i.op = M.presheaf.map (f.opensFunctor.map i).op := rfl

/-- The original restriction-composition comparison respects the native adjunctions. -/
theorem moduleRestrictionComp_homEquiv (M : Z.Modules) (N : X.Modules)
    (k : M.restrict (f ≫ g) ⟶ N) :
    ((Scheme.Modules.restrictAdjunction g).comp (Scheme.Modules.restrictAdjunction f)).homEquiv _ _
      ((Scheme.Modules.restrictFunctorComp f g).inv.app M ≫ k) =
    (Scheme.Modules.restrictAdjunction (f ≫ g)).homEquiv _ _ k ≫
      (Scheme.Modules.pushforwardComp f g).inv.app N := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_inv_app_app, AddCommGrpCat.comp_apply,
    Functor.comp_map, Adjunction.comp_unit_app,
    Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app, moduleRestriction_presheaf_map]
  let W := f ⁻¹ᵁ (g ⁻¹ᵁ U)
  change k.app W
    (M.presheaf.map (eqToHom (show (f ≫ g) ''ᵁ W = g ''ᵁ (f ''ᵁ W) by
      rw [Scheme.Hom.comp_image])).op
      (M.presheaf.map (g.opensFunctor.map (homOfLE (f.image_preimage_le (g ⁻¹ᵁ U)))).op
        (M.presheaf.map (homOfLE (g.image_preimage_le U)).op x))) =
      k.app W (M.presheaf.map (homOfLE ((f ≫ g).image_preimage_le U)).op x)
  let h₁ := homOfLE (g.image_preimage_le U)
  let h₂ := g.opensFunctor.map (homOfLE (f.image_preimage_le (g ⁻¹ᵁ U)))
  let h₃ := eqToHom (show (f ≫ g) ''ᵁ W = g ''ᵁ (f ''ᵁ W) by rw [Scheme.Hom.comp_image])
  let h₄ := homOfLE ((f ≫ g).image_preimage_le U)
  have hm : M.presheaf.map h₁.op ≫ M.presheaf.map h₂.op ≫ M.presheaf.map h₃.op =
      M.presheaf.map h₄.op := by
    rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
    congr 1
  exact congrArg (fun z => k.app W z) (ConcreteCategory.congr_hom hm x)

/-- The native restriction-to-pullback comparisons respect the composite adjunction. -/
theorem moduleRestrictionPullback_comp_homEquiv (M : Z.Modules) (N : X.Modules)
    (k : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ⟶ N) :
    ((Scheme.Modules.restrictAdjunction g).comp (Scheme.Modules.restrictAdjunction f)).homEquiv _ _
      ((Scheme.Modules.restrictFunctor f).map ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M) ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app ((Scheme.Modules.pullback g).obj M) ≫ k) =
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv _ _ k := by
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  change (Scheme.Modules.restrictAdjunction g).homEquiv M ((Scheme.Modules.pushforward f).obj N)
    ((Scheme.Modules.restrictAdjunction f).homEquiv ((Scheme.Modules.restrictFunctor g).obj M) N
      ((Scheme.Modules.restrictFunctor f).map ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M) ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app ((Scheme.Modules.pullback g).obj M) ≫ k)) =
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv M ((Scheme.Modules.pushforward f).obj N)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv ((Scheme.Modules.pullback g).obj M) N k)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [Scheme.Modules.restrictFunctorIsoPullback,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [Adjunction.homEquiv_naturality_right]
  simp only [Adjunction.homEquiv_unit,
    Functor.map_comp, Category.assoc]
  have hf := (Scheme.Modules.restrictAdjunction f).unit_leftAdjointUniq_hom_app
    (Scheme.Modules.pullbackPushforwardAdjunction f) ((Scheme.Modules.pullback g).obj M)
  have hfm := congrArg (Scheme.Modules.pushforward g).map hf
  simpa only [Functor.map_comp, Category.assoc] using! congrArg
    (fun q => (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫ q ≫
      (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward f).map k)) hfm

/-- The original restriction-to-pullback comparison commutes with composition. -/
theorem moduleRestrictionPullback_comp (M : Z.Modules) :
    (Scheme.Modules.restrictFunctorComp f g).hom.app M ≫
      (Scheme.Modules.restrictFunctor f).map ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app M) ≫
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.app ((Scheme.Modules.pullback g).obj M) ≫
      (Scheme.Modules.pullbackComp f g).hom.app M =
        (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom.app M := by
  apply (cancel_epi ((Scheme.Modules.restrictFunctorComp f g).inv.app M)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  apply (((Scheme.Modules.restrictAdjunction g).comp
    (Scheme.Modules.restrictAdjunction f)).homEquiv _ _).injective
  rw [moduleRestrictionPullback_comp_homEquiv]
  have hL := modulePullbackComp_homEquiv f g M
    ((Scheme.Modules.pullback (f ≫ g)).obj M) (𝟙 _)
  simp only [Category.comp_id] at hL
  rw [hL, moduleRestrictionComp_homEquiv]
  rw [Scheme.Modules.restrictFunctorIsoPullback, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [Adjunction.homEquiv_unit]
  change ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫ 𝟙 _) ≫ _ = _
  simp only [Category.comp_id]

end BPFixedPoints.SheafTools
