import BPFixedPoints.Incidence.VertexMapPullbackTwist

/-!
# Pulled back local frames on pulled back sections

Let `g : X ⟶ Y` be a morphism of schemes, `M` a sheaf of modules on `Y` with a rank-one frame
`e : M|_U ≅ 𝒪_U` on an open `U`, and `X'` an open of `X` mapped into `U` by a lift `k`. The frame
of `g^* M` on `X'` obtained by restricting, composing pullbacks and pulling back `e` along `k`
(`pullLocalFrame`; it is the shape of the chart frames `vertexTwistPullChartIso` of
`VertexMapPullbackTwist`) is computed on pulled back sections, i.e. on the images of sections
under the unit `M ⟶ g_* g^* M` of the module adjunction.

Proved here, from the adjunctions alone (no exactness of the pullback is used):
* the adjoint of the pulled back local frame along the composite map is the frame on `U` followed
  by the comorphism of the lift (`modulePullbackLocalUnitIso_homEquiv`), and restricting a
  pullback to an open is adjoint to the pullback along the composite
  (`pullbackRestrict_homEquiv`);
* the coefficient of the over-site frame is the value of the frame on the open subscheme
  (`moduleOverUnitIso_coefficient`, definitional);
* **coefficients of pulled back sections** (`pullLocalFrame_coefficient`): on an open `S ⊆ X'`
  over the preimage of an open `O ⊆ U`, the frame coefficient of the pulled back section of `s` is
  the pullback `g^♯` of the frame coefficient of `s`, restricted to `S`.

Nothing here is specific to projective lines.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace SheafTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000

section Frames

variable {X Y : Scheme.{0}}

/-- The restriction-to-pullback comparison is the unit of the pullback adjunction under the
restriction adjunction. -/
theorem restrictAdjunction_homEquiv_restrictFunctorIsoPullback {X' : Scheme.{0}} (j : X' ⟶ X)
    [IsOpenImmersion j] (N : X.Modules) (P : X'.Modules)
    (t : (Scheme.Modules.pullback j).obj N ⟶ P) :
    (Scheme.Modules.restrictAdjunction j).homEquiv _ _
        ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N ≫ t) =
      (Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _ t := by
  rw [Adjunction.homEquiv_naturality_right, Scheme.Modules.restrictFunctorIsoPullback,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]

/-- **Fact for local frames.** The adjoint of the pulled back local frame is the frame of the
restriction followed by the comorphism of the lift. -/
theorem modulePullbackLocalUnitIso_homEquiv (h : X ⟶ Y) (U : Y.Opens) (M : Y.Modules)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (k : X ⟶ U)
    (hk : k ≫ U.ι = h) :
    (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
        (modulePullbackLocalUnitIso h U M e k hk).hom =
      (Scheme.Modules.restrictAdjunction U.ι).homEquiv _ _
          (e.hom ≫ SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp k U.ι).hom.app _ ≫
          (Scheme.Modules.pushforwardCongr hk).hom.app _ := by
  subst hk
  have hc : (Scheme.Modules.pushforwardCongr (rfl : k ≫ U.ι = k ≫ U.ι)).hom.app
      (SheafOfModules.unit X.ringCatSheaf) = 𝟙 _ := by
    apply Scheme.Modules.hom_ext
    intro W
    rw [Scheme.Modules.pushforwardCongr_hom_app_app]
    simp
  rw [hc, Category.comp_id]
  have hd : (modulePullbackLocalUnitIso (k ≫ U.ι) U M e k rfl).hom =
      (Scheme.Modules.pullbackComp k U.ι).inv.app M ≫
        ((Scheme.Modules.pullback k).map ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M ≫
          e.hom) ≫ (modulePullbackUnitIso k).hom) := by
    dsimp only [modulePullbackLocalUnitIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
      Functor.mapIso_hom]
    rw [modulePullbackCongr_hom]
    simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp]
  have hL := modulePullbackComp_homEquiv k U.ι M (SheafOfModules.unit X.ringCatSheaf)
    ((Scheme.Modules.pullbackComp k U.ι).inv.app M ≫
        ((Scheme.Modules.pullback k).map ((Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app M ≫
          e.hom) ≫ (modulePullbackUnitIso k).hom))
  rw [Iso.hom_inv_id_app_assoc, Adjunction.comp_homEquiv] at hL
  have hL' := (Iso.comp_inv_eq ((Scheme.Modules.pushforwardComp k U.ι).app
    (SheafOfModules.unit X.ringCatSheaf))).mp hL.symm
  rw [hd, Iso.app_hom] at *
  rw [hL']
  congr 1
  change (Scheme.Modules.pullbackPushforwardAdjunction U.ι).homEquiv _ _
    ((Scheme.Modules.pullbackPushforwardAdjunction k).homEquiv _ _ _) = _
  rw [Adjunction.homEquiv_naturality_left, modulePullbackUnitIso_adjunction,
    ← restrictAdjunction_homEquiv_restrictFunctorIsoPullback, ← Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rfl

/-- **Fact for restricted pullbacks.** Restricting a pullback to an open and composing pullbacks
is adjoint to the pullback along the composite. -/
theorem pullbackRestrict_homEquiv (g : X ⟶ Y) (M : Y.Modules) (X' : X.Opens)
    (P : X'.toScheme.Modules) (φ : (Scheme.Modules.pullback (X'.ι ≫ g)).obj M ⟶ P) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.restrictAdjunction X'.ι)).homEquiv _ _
      ((Scheme.Modules.restrictFunctorIsoPullback X'.ι).hom.app ((Scheme.Modules.pullback g).obj M) ≫
        (Scheme.Modules.pullbackComp X'.ι g).hom.app M ≫ φ) =
      (Scheme.Modules.pullbackPushforwardAdjunction (X'.ι ≫ g)).homEquiv _ _ φ ≫
        (Scheme.Modules.pushforwardComp X'.ι g).inv.app P := by
  rw [Adjunction.comp_homEquiv]
  change (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
    ((Scheme.Modules.restrictAdjunction X'.ι).homEquiv _ _ _) = _
  rw [restrictAdjunction_homEquiv_restrictFunctorIsoPullback]
  have h := modulePullbackComp_homEquiv X'.ι g M P φ
  rw [Adjunction.comp_homEquiv] at h
  exact h

/-- The image of the preimage of an open contained in an open subscheme is the open. -/
theorem schemeOpensImagePreimage {Z : Scheme.{0}} (U : Z.Opens) {S : Z.Opens} (hS : S ≤ U) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ S) = S := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  simp only [Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr hS

/-- The coefficients of an over-site frame are the values of the frame on the open subscheme. -/
theorem moduleOverUnitIso_coefficient {Z : Scheme.{0}} (M : Z.Modules) (U : Z.Opens)
    (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) {S : Z.Opens} (hS : S ≤ U)
    (x : Γ(M, S)) :
    ((moduleOverUnitIso Z M U e).hom.val.app (op (Over.mk (homOfLE hS)))).hom x =
      Z.presheaf.map (eqToHom (schemeOpensImagePreimage U hS).symm).op ((e.hom.app (U.ι ⁻¹ᵁ S)).hom
        (M.presheaf.map (eqToHom (schemeOpensImagePreimage U hS)).op x)) :=
  rfl

variable (g : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
  (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (X' : X.Opens)
  (k : X'.toScheme ⟶ U.toScheme) (hk : k ≫ U.ι = X'.ι ≫ g)

/-- **The pulled back local frame** of a sheaf of modules with a frame on `U`, on an open `X'`
mapped into `U`. -/
noncomputable def pullLocalFrame :
    ((Scheme.Modules.pullback g).obj M).restrict X'.ι ≅
      SheafOfModules.unit X'.toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback X'.ι).app _ ≪≫
    (Scheme.Modules.pullbackComp X'.ι g).app M ≪≫ modulePullbackLocalUnitIso _ U M e k hk

include hk in
/-- The preimage of an open along the composite is contained in its preimage along the lift. -/
theorem pullLocalFrame_preimage_le (O : Y.Opens) : X'.ι ⁻¹ᵁ (g ⁻¹ᵁ O) ≤ k ⁻¹ᵁ (U.ι ⁻¹ᵁ O) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hk]

/-- **The pulled back frame on pulled back sections**, on the preimage of an open. -/
theorem pullLocalFrame_app (O : Y.Opens) (s : Γ(M, O)) :
    ((pullLocalFrame g M U e X' k hk).hom.app (X'.ι ⁻¹ᵁ (g ⁻¹ᵁ O))).hom
        (((Scheme.Modules.pullback g).obj M).presheaf.map
          (homOfLE (X'.ι.image_preimage_le (g ⁻¹ᵁ O))).op
          (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app O s)) =
      X'.toScheme.presheaf.map (homOfLE (pullLocalFrame_preimage_le g U X' k hk O)).op
        (k.app (U.ι ⁻¹ᵁ O) ((e.hom.app (U.ι ⁻¹ᵁ O)).hom
          (M.presheaf.map (homOfLE (U.ι.image_preimage_le O)).op s))) := by
  have hB := pullbackRestrict_homEquiv g M X' (SheafOfModules.unit X'.toScheme.ringCatSheaf)
    (modulePullbackLocalUnitIso (X'.ι ≫ g) U M e k hk).hom
  rw [modulePullbackLocalUnitIso_homEquiv] at hB
  have h1 := congrArg (fun t => (t.app O).hom s) hB
  simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app] at h1
  refine Eq.trans ?_ (h1.trans ?_)
  · rfl
  · simp only [Scheme.Modules.pushforwardComp_inv_app_app, Scheme.Modules.pushforwardComp_hom_app_app,
      Scheme.Modules.pushforwardCongr_hom_app_app, Scheme.Modules.pushforward_map_app,
      Scheme.Modules.restrictAdjunction_unit_app_app, Scheme.Modules.Hom.comp_app,
      Category.comp_id, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
    exact congrArg (fun m => (X'.toScheme.presheaf.map m).hom (k.app (U.ι ⁻¹ᵁ O)
      ((e.hom.app (U.ι ⁻¹ᵁ O)).hom (M.presheaf.map (homOfLE (U.ι.image_preimage_le O)).op s))))
      (Subsingleton.elim _ _)

/-- Two successive restrictions of functions are one restriction. -/
theorem schemePresheaf_map_map {Z : Scheme.{0}} {A B C' : Z.Opens} (m₁ : op A ⟶ op B)
    (m₂ : op B ⟶ op C') (m₃ : op A ⟶ op C') (x : Γ(Z, A)) :
    Z.presheaf.map m₂ (Z.presheaf.map m₁ x) = Z.presheaf.map m₃ x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim (m₁ ≫ m₂) m₃]

/-- Two successive restrictions of sections of a module are one restriction. -/
theorem modulePresheaf_map_map {Z : Scheme.{0}} (N : Z.Modules) {A B C' : Z.Opens}
    (m₁ : op A ⟶ op B) (m₂ : op B ⟶ op C') (m₃ : op A ⟶ op C') (x : Γ(N, A)) :
    N.presheaf.map m₂ (N.presheaf.map m₁ x) = N.presheaf.map m₃ x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim (m₁ ≫ m₂) m₃]

include hk in
/-- The comorphism of the lift is the restricted comorphism of `g`. -/
theorem pullLocalFrame_lift_app (O : Y.Opens) (hO : O ≤ U) (r : Γ(U.toScheme, U.ι ⁻¹ᵁ O)) :
    X'.toScheme.presheaf.map (homOfLE (pullLocalFrame_preimage_le g U X' k hk O)).op (k.app (U.ι ⁻¹ᵁ O) r) =
      X'.ι.app (g ⁻¹ᵁ O) (g.app O (Y.presheaf.map (eqToHom (schemeOpensImagePreimage U hO).symm).op r)) := by
  set t := Y.presheaf.map (eqToHom (schemeOpensImagePreimage U hO).symm).op r with ht
  have hr : U.ι.app O t = r := by
    rw [Scheme.Opens.ι_app]
    exact (schemePresheaf_map_map (Z := Y) _ _ (𝟙 _) r).trans
      (by rw [CategoryTheory.Functor.map_id]; rfl)
  have hc : k.app (U.ι ⁻¹ᵁ O) (U.ι.app O t) =
      X'.toScheme.presheaf.map (eqToHom (by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hk])).op
        (X'.ι.app (g ⁻¹ᵁ O) (g.app O t)) :=
    congrArg (fun m => m t) (Scheme.Hom.congr_app hk O)
  rw [← hr, hc]
  exact (schemePresheaf_map_map (Z := X'.toScheme) _ _ (𝟙 _) _).trans
    (by rw [CategoryTheory.Functor.map_id]; rfl)

/-- **Coefficients of pulled back sections in the pulled back frame.** On an open `S` of `X'` over
the preimage of an open `O ⊆ U`, the frame coefficient of the restriction of the pulled back
section of `s` is the restriction of the pullback of the frame coefficient of `s`. -/
theorem pullLocalFrame_coefficient (O : Y.Opens) (hO : O ≤ U) (S : X.Opens) (hS : S ≤ X')
    (hSO : S ≤ g ⁻¹ᵁ O) (s : Γ(M, O)) :
    ((moduleOverUnitIso X ((Scheme.Modules.pullback g).obj M) X'
        (pullLocalFrame g M U e X' k hk)).hom.val.app (op (Over.mk (homOfLE hS)))).hom
        (((Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE hSO).op
          (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app O s)) =
      X.presheaf.map (homOfLE hSO).op
        (g.app O (((moduleOverUnitIso Y M U e).hom.val.app (op (Over.mk (homOfLE hO)))).hom s)) := by
  rw [moduleOverUnitIso_coefficient, moduleOverUnitIso_coefficient]
  have hSle : X'.ι ⁻¹ᵁ S ≤ X'.ι ⁻¹ᵁ (g ⁻¹ᵁ O) := X'.ι.preimage_mono hSO
  have key : ∀ y : Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ O),
      ((pullLocalFrame g M U e X' k hk).hom.app (X'.ι ⁻¹ᵁ S)).hom
        (((Scheme.Modules.pullback g).obj M).presheaf.map (eqToHom (schemeOpensImagePreimage X' hS)).op
          (((Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE hSO).op y)) =
      X'.toScheme.presheaf.map (homOfLE hSle).op
        (((pullLocalFrame g M U e X' k hk).hom.app (X'.ι ⁻¹ᵁ (g ⁻¹ᵁ O))).hom
          (((Scheme.Modules.pullback g).obj M).presheaf.map
            (homOfLE (X'.ι.image_preimage_le (g ⁻¹ᵁ O))).op y)) := by
    intro y
    have h2 := ConcreteCategory.congr_hom
      ((pullLocalFrame g M U e X' k hk).hom.mapPresheaf.naturality (homOfLE hSle).op)
      (((Scheme.Modules.pullback g).obj M).presheaf.map
        (homOfLE (X'.ι.image_preimage_le (g ⁻¹ᵁ O))).op y)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h2
    have harg : ((Scheme.Modules.pullback g).obj M).presheaf.map
        (eqToHom (schemeOpensImagePreimage X' hS)).op
          (((Scheme.Modules.pullback g).obj M).presheaf.map (homOfLE hSO).op y) =
        (((Scheme.Modules.pullback g).obj M).restrict X'.ι).presheaf.map (homOfLE hSle).op
          (((Scheme.Modules.pullback g).obj M).presheaf.map
            (homOfLE (X'.ι.image_preimage_le (g ⁻¹ᵁ O))).op y) := by
      rw [moduleRestriction_presheaf_map]
      exact (modulePresheaf_map_map _ _ _ (homOfLE (show X'.ι ''ᵁ (X'.ι ⁻¹ᵁ S) ≤ g ⁻¹ᵁ O from
        (X'.ι.image_preimage_le S).trans hSO)).op y).trans
        (modulePresheaf_map_map _ _ _ _ y).symm
    rw [harg]
    exact h2
  erw [key, pullLocalFrame_app]
  have hm : M.presheaf.map (eqToHom (schemeOpensImagePreimage U hO)).op =
      M.presheaf.map (homOfLE (U.ι.image_preimage_le O)).op := by
    rw [Subsingleton.elim (eqToHom (schemeOpensImagePreimage U hO)).op
      (homOfLE (U.ι.image_preimage_le O)).op]
  rw [hm, pullLocalFrame_lift_app g U X' k hk O hO, Scheme.Opens.ι_app, Scheme.Opens.toScheme_presheaf_map]
  erw [schemePresheaf_map_map (Z := X) _ _
      (homOfLE ((X'.ι.image_preimage_le S).trans hSO)).op,
    schemePresheaf_map_map (Z := X) _ _ (homOfLE hSO).op]

end Frames

end BPFixedPoints.Multigraph
