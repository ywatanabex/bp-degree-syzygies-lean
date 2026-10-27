import BPFixedPoints.Incidence.VertexPermutationTwistFrames

/-!
# Transport of the multi-twist sheaves along a vertex bijection

For a bijection `ψ : V ≃ W` let `g = a_{ψ⁻¹} : (P¹)^V ≅ (P¹)^W` be the coordinate map of `ψ⁻¹`
(`vertexSchemePerm R ψ.symm`, an isomorphism of schemes over the base). It pulls back the chart of
`τ : W → Fin 2` to the chart of `τ ∘ ψ`, and pair intersections of charts to pair intersections
(`vertexSchemePerm_symm_preimage_chartOpen`, `..._chartPairOpen`).

For twists `a : V → ℤ` and `b : W → ℤ` with `b ∘ ψ = a`, the pushforward `g_* O(a)` and `O(b)` are
compared chart by chart: on the chart of `τ` the comparison is the chart frame of `O(a)` on the
chart of `τ ∘ ψ`, transported along `g` (`VertexPermutationTwistFrames.lean`), followed by the
inverse chart frame of `O(b)`. The transported transition units are the transition units of
`O(b)`: the factor unit of the vertex `ψ v` is the pullback, along the lift of the projection of
`ψ v`, of the same Laurent unit as the factor unit of `v`, and `g` followed by the projection of
`ψ v` is the projection of `v` (`vertexTwistSheafPairUnit_perm`). The chart comparisons therefore
glue (`moduleFrameGlueIso`) to an isomorphism of sheaves of modules
`vertexTwistPermIso : g_* O(a) ≅ O(b)`. It is built from the scheme isomorphism and the frames,
not from cohomology or states.

Proved here:
* the gluing and the chart restrictions of the transport (`vertexTwistPermIso_over`,
  `vertexTwistPermIso_chart`);
* the chart coefficients of a transported section are the inverse structure maps of the chart
  coefficients of the original section on the preimage (`vertexTwistPermIso_chartCoefficient`);
* the underlying abelian sheaf of `g_* M` is literally the image of the underlying abelian sheaf
  of `M` under `vertexSheafPerm R ψ` (`vertexSheafPerm_obj_toSheaf`), so the transport gives
  `vertexTwistAbelianPermIso : (vertexSheafPerm R ψ).functor.obj O(a) ≅ O(b)`, and
  `vertexTwistAbelianPermIsoSymm` for `b = a ∘ ψ⁻¹`.

Not proved here: compatibility with the mixed face coordinates of the cubical cell route, the
effect on the state coordinates of cohomology, and compatibility with the tensor products of
twists.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace SheafTools
open ProjectiveLine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000

/-- A lift through an open subscheme lands in the preimage of that open. -/
theorem le_preimage_of_lift {X Y : Scheme.{0}} (p : X ⟶ Y) (U : X.Opens) (O : Y.Opens)
    (k : U.toScheme ⟶ O.toScheme) (hk : k ≫ O.ι = U.ι ≫ p) : U ≤ p ⁻¹ᵁ O := by
  intro x hx
  have h : p x = O.ι (k ⟨x, hx⟩) := by
    rw [← Scheme.Hom.comp_apply, hk]
    rfl
  change p x ∈ O
  rw [h]
  exact (k ⟨x, hx⟩).2

variable (R : Type) [CommRing R] {V W : Type} [Fintype V] [Fintype W] (ψ : V ≃ W)

instance vertexSchemePerm_isIso : IsIso (vertexSchemePerm R ψ) :=
  inferInstanceAs (IsIso (vertexSchemePermIso R ψ).hom)

/-- The coordinate map of `ψ⁻¹` followed by the projection of `ψ v` is the projection of `v`. -/
theorem vertexSchemePerm_symm_projection_apply (v : V) :
    vertexSchemePerm R ψ.symm ≫ (vertexProjectionOver R W (ψ v)).left =
      (vertexProjectionOver R V v).left := by
  rw [vertexSchemePerm_projection, Equiv.symm_apply_apply]

/-- The coordinate map of `ψ⁻¹` pulls back the chart of `τ` to the chart of `τ ∘ ψ`. -/
theorem vertexSchemePerm_symm_preimage_chartOpen (τ : W → Fin 2) :
    vertexSchemePerm R ψ.symm ⁻¹ᵁ vertexChartOpen R W τ = vertexChartOpen R V (fun v => τ (ψ v)) := by
  ext x
  have hp : ∀ v, (vertexProjectionOver R W (ψ v)).left (vertexSchemePerm R ψ.symm x) =
      (vertexProjectionOver R V v).left x := fun v =>
    congrArg (fun f => f x) (vertexSchemePerm_symm_projection_apply R ψ v)
  change vertexSchemePerm R ψ.symm x ∈ vertexChartOpen R W τ ↔ x ∈ vertexChartOpen R V _
  rw [mem_vertexChartOpen, mem_vertexChartOpen]
  constructor
  · intro h v
    rw [← hp]
    exact h (ψ v)
  · intro h w
    have hw := h (ψ.symm w)
    rw [← hp, Equiv.apply_symm_apply] at hw
    exact hw

/-- The coordinate map of `ψ⁻¹` pulls back pair intersections of charts. -/
theorem vertexSchemePerm_symm_preimage_chartPairOpen (τ τ' : W → Fin 2) :
    vertexSchemePerm R ψ.symm ⁻¹ᵁ vertexChartPairOpen R W τ τ' =
      vertexChartPairOpen R V (fun v => τ (ψ v)) (fun v => τ' (ψ v)) := by
  rw [vertexChartPairOpen, vertexChartPairOpen, Scheme.Hom.preimage_inf,
    vertexSchemePerm_symm_preimage_chartOpen, vertexSchemePerm_symm_preimage_chartOpen]

variable (a : V → ℤ) (b : W → ℤ) (hb : ∀ v, b (ψ v) = a v)

/-- The pushforward of the multi-twist of `V` along the coordinate map of `ψ⁻¹`. -/
noncomputable abbrev vertexTwistPushforward : (vertexScheme R W).Modules :=
  (Scheme.Modules.pushforward (vertexSchemePerm R ψ.symm)).obj (vertexTwistSheaf R V a)

/-- The chart frame of `τ ∘ ψ`, transported to the chart of `τ`. -/
noncomputable def vertexTwistPermChartFrame (τ : W → Fin 2) :
    (vertexTwistPushforward R ψ a).over (vertexChartOpen R W τ) ≅
      SheafOfModules.unit ((vertexScheme R W).ringCatSheaf.over (vertexChartOpen R W τ)) :=
  pushforwardOverFrame (vertexSchemePerm R ψ.symm) (vertexTwistSheaf R V a)
    (vertexSchemePerm_symm_preimage_chartOpen R ψ τ).le
    (vertexTwistOverChartIso R V a (fun v => τ (ψ v)))

/-- The pair frame of `(τ ∘ ψ, τ' ∘ ψ)`, transported to the pair intersection of `τ` and `τ'`. -/
noncomputable def vertexTwistPermPairFrame (τ τ' : W → Fin 2) (right : Bool) :
    (vertexTwistPushforward R ψ a).over (vertexChartPairOpen R W τ τ') ≅
      SheafOfModules.unit ((vertexScheme R W).ringCatSheaf.over (vertexChartPairOpen R W τ τ')) :=
  pushforwardOverFrame (vertexSchemePerm R ψ.symm) (vertexTwistSheaf R V a)
    (vertexSchemePerm_symm_preimage_chartPairOpen R ψ τ τ').le
    (vertexTwistOverPairIso R V a (fun v => τ (ψ v)) (fun v => τ' (ψ v)) right)

theorem vertexTwistPermChartFrame_left (τ τ' : W → Fin 2) :
    moduleOverFrameRestriction (vertexScheme R W) (homOfLE (show vertexChartPairOpen R W τ τ' ≤
      vertexChartOpen R W τ from inf_le_left)) (vertexTwistPushforward R ψ a)
        (vertexTwistPermChartFrame R ψ a τ) = vertexTwistPermPairFrame R ψ a τ τ' false := by
  rw [vertexTwistPermChartFrame, pushforwardOverFrame_restriction, vertexTwistPermPairFrame,
    ← vertexTwistOverChartIso_left R V a (fun v => τ (ψ v)) (fun v => τ' (ψ v)),
    pushforwardOverFrame_restrict_source]

theorem vertexTwistPermChartFrame_right (τ τ' : W → Fin 2) :
    moduleOverFrameRestriction (vertexScheme R W) (homOfLE (show vertexChartPairOpen R W τ τ' ≤
      vertexChartOpen R W τ' from inf_le_right)) (vertexTwistPushforward R ψ a)
        (vertexTwistPermChartFrame R ψ a τ') = vertexTwistPermPairFrame R ψ a τ τ' true := by
  rw [vertexTwistPermChartFrame, pushforwardOverFrame_restriction, vertexTwistPermPairFrame,
    ← vertexTwistOverChartIso_right R V a (fun v => τ (ψ v)) (fun v => τ' (ψ v)),
    pushforwardOverFrame_restrict_source]

include hb in
/-- The transported transition units are the transition units of the relabeled twist. -/
theorem vertexTwistSheafPairUnit_perm (τ τ' : W → Fin 2) :
    (vertexSchemePerm R ψ.symm).app (vertexChartPairOpen R W τ τ')
        ((vertexChartPairOpen R W τ τ').topIso.hom
          (vertexTwistSheafPairUnit R W b τ τ' : Γ((vertexChartPairOpen R W τ τ').toScheme, ⊤))) =
      (vertexScheme R V).presheaf.map (homOfLE (vertexSchemePerm_symm_preimage_chartPairOpen R ψ τ τ').le).op
        ((vertexChartPairOpen R V (fun v => τ (ψ v)) (fun v => τ' (ψ v))).topIso.hom
          (vertexTwistSheafPairUnit R V a (fun v => τ (ψ v)) (fun v => τ' (ψ v)) :
            Γ((vertexChartPairOpen R V (fun v => τ (ψ v)) (fun v => τ' (ψ v))).toScheme, ⊤))) := by
  simp only [vertexTwistSheafPairUnit, Units.coe_prod, map_prod]
  rw [← Fintype.prod_equiv ψ (fun v => _) _ (fun _ => rfl)]
  refine Finset.prod_congr rfl fun v _ => ?_
  change (vertexSchemePerm R ψ.symm).app (vertexChartPairOpen R W τ τ')
      ((vertexChartPairOpen R W τ τ').topIso.hom
        ((vertexChartPairProjectionLift R W τ τ' (ψ v)).appTop
          (twistSheafPairUnit R (b (ψ v)) (τ (ψ v)) (τ' (ψ v)) :
            Γ((standardPairOpen R (τ (ψ v)) (τ' (ψ v))).toScheme, ⊤)))) =
    (vertexScheme R V).presheaf.map
      (homOfLE (vertexSchemePerm_symm_preimage_chartPairOpen R ψ τ τ').le).op
      ((vertexChartPairOpen R V (fun v => τ (ψ v)) (fun v => τ' (ψ v))).topIso.hom
        ((vertexChartPairProjectionLift R V (fun v => τ (ψ v)) (fun v => τ' (ψ v)) v).appTop
          (twistSheafPairUnit R (a v) (τ (ψ v)) (τ' (ψ v)) :
            Γ((standardPairOpen R (τ (ψ v)) (τ' (ψ v))).toScheme, ⊤))))
  rw [hb v]
  exact app_topIso_appTop_lift (vertexSchemePerm R ψ.symm) (vertexProjectionOver R W (ψ v)).left
    (vertexProjectionOver R V v).left (vertexSchemePerm_symm_projection_apply R ψ v) _ _
    (vertexSchemePerm_symm_preimage_chartPairOpen R ψ τ τ').le _ _
    (vertexChartPairProjectionLift_fac R W τ τ' (ψ v)) _
    (vertexChartPairProjectionLift_fac R V _ _ v)
    (le_preimage_of_lift _ _ _ _ (vertexChartPairProjectionLift_fac R W τ τ' (ψ v)))
    (le_preimage_of_lift _ _ _ _ (vertexChartPairProjectionLift_fac R V _ _ v)) _

include hb in
/-- The transported pair frames have the transition of the relabeled twist. -/
theorem vertexTwistPermPairFrame_transition (τ τ' : W → Fin 2) :
    (vertexTwistPermPairFrame R ψ a τ τ' false).hom =
      (vertexTwistPermPairFrame R ψ a τ τ' true).hom ≫
        moduleOverMultiplication (vertexScheme R W) (vertexChartPairOpen R W τ τ')
          (vertexTwistSheafPairUnit R W b τ τ' : Γ((vertexChartPairOpen R W τ τ').toScheme, ⊤)) :=
  pushforwardOverFrame_transition _ _ _ _ _ _ _
    (vertexTwistOverPairIso_transition R V a _ _) (vertexTwistSheafPairUnit_perm R ψ a b hb τ τ')

/-- The chart comparison: the transported chart frame followed by the inverse chart frame of the
relabeled twist. -/
noncomputable def vertexTwistPermLocalIso (τ : W → Fin 2) :
    (vertexTwistPushforward R ψ a).over (vertexChartOpen R W τ) ≅
      (vertexTwistSheaf R W b).over (vertexChartOpen R W τ) :=
  vertexTwistPermChartFrame R ψ a τ ≪≫ (vertexTwistOverChartIso R W b τ).symm

include hb in
theorem vertexTwistPermLocal_hom_compatible :
    TopCat.Presheaf.IsCompatible (X := TopCat.of (vertexScheme R W))
      (moduleHomSheaf (vertexScheme R W) (vertexTwistPushforward R ψ a)
        (vertexTwistSheaf R W b)).obj (vertexChartOpen R W)
      (fun τ => moduleOverHomSection (vertexScheme R W) _ _ (vertexChartOpen R W τ)
        (vertexTwistPermLocalIso R ψ a b τ).hom) := by
  intro τ τ'
  dsimp only [vertexTwistPermLocalIso, Iso.trans_hom, Iso.symm_hom]
  rw [moduleFrameMap_section_restrict, moduleFrameMap_section_restrict]
  have hL : Opens.infLELeft (vertexChartOpen R W τ) (vertexChartOpen R W τ') =
      homOfLE (show vertexChartPairOpen R W τ τ' ≤ vertexChartOpen R W τ from inf_le_left) :=
    Subsingleton.elim _ _
  have hR : Opens.infLERight (vertexChartOpen R W τ) (vertexChartOpen R W τ') =
      homOfLE (show vertexChartPairOpen R W τ τ' ≤ vertexChartOpen R W τ' from inf_le_right) :=
    Subsingleton.elim _ _
  rw [hL, hR, vertexTwistPermChartFrame_left, vertexTwistPermChartFrame_right,
    vertexTwistOverChartIso_left, vertexTwistOverChartIso_right]
  congr 1
  exact moduleFrameMap_eq_of_transition (vertexScheme R W)
    (vertexTwistPermPairFrame R ψ a τ τ' false) (vertexTwistPermPairFrame R ψ a τ τ' true)
    (vertexTwistOverPairIso R W b τ τ' false) (vertexTwistOverPairIso R W b τ τ' true) _
    (vertexTwistPermPairFrame_transition R ψ a b hb τ τ') (vertexTwistOverPairIso_transition R W b τ τ')

include hb in
theorem vertexTwistPermLocal_inv_compatible :
    TopCat.Presheaf.IsCompatible (X := TopCat.of (vertexScheme R W))
      (moduleHomSheaf (vertexScheme R W) (vertexTwistSheaf R W b)
        (vertexTwistPushforward R ψ a)).obj (vertexChartOpen R W)
      (fun τ => moduleOverHomSection (vertexScheme R W) _ _ (vertexChartOpen R W τ)
        (vertexTwistPermLocalIso R ψ a b τ).inv) := by
  intro τ τ'
  dsimp only [vertexTwistPermLocalIso, Iso.trans_inv, Iso.symm_inv]
  rw [moduleFrameMap_section_restrict, moduleFrameMap_section_restrict]
  have hL : Opens.infLELeft (vertexChartOpen R W τ) (vertexChartOpen R W τ') =
      homOfLE (show vertexChartPairOpen R W τ τ' ≤ vertexChartOpen R W τ from inf_le_left) :=
    Subsingleton.elim _ _
  have hR : Opens.infLERight (vertexChartOpen R W τ) (vertexChartOpen R W τ') =
      homOfLE (show vertexChartPairOpen R W τ τ' ≤ vertexChartOpen R W τ' from inf_le_right) :=
    Subsingleton.elim _ _
  rw [hL, hR, vertexTwistPermChartFrame_left, vertexTwistPermChartFrame_right,
    vertexTwistOverChartIso_left, vertexTwistOverChartIso_right]
  congr 1
  exact moduleFrameMap_eq_of_transition (vertexScheme R W)
    (vertexTwistOverPairIso R W b τ τ' false) (vertexTwistOverPairIso R W b τ τ' true)
    (vertexTwistPermPairFrame R ψ a τ τ' false) (vertexTwistPermPairFrame R ψ a τ τ' true) _
    (vertexTwistOverPairIso_transition R W b τ τ') (vertexTwistPermPairFrame_transition R ψ a b hb τ τ')

/-- **Transport of the multi-twist along a vertex bijection.** The pushforward of `O(a)` on
`(P¹)^V` along the coordinate map of `ψ⁻¹` is `O(b)` on `(P¹)^W` whenever `b ∘ ψ = a`, glued from
the transported chart frames. -/
noncomputable def vertexTwistPermIso :
    vertexTwistPushforward R ψ a ≅ vertexTwistSheaf R W b :=
  moduleFrameGlueIso (vertexScheme R W) _ _ (vertexChartOpen R W) (vertexChartOpen_iSup_top R W)
    (vertexTwistPermLocalIso R ψ a b) (vertexTwistPermLocal_hom_compatible R ψ a b hb)
      (vertexTwistPermLocal_inv_compatible R ψ a b hb)

/-- The transport restricts on every chart to the specified chart comparison. -/
theorem vertexTwistPermIso_over (τ : W → Fin 2) :
    (SheafOfModules.overFunctor (vertexScheme R W).ringCatSheaf (vertexChartOpen R W τ)).mapIso
      (vertexTwistPermIso R ψ a b hb) = vertexTwistPermLocalIso R ψ a b τ :=
  moduleFrameGlueIso_over (vertexScheme R W) _ _ (vertexChartOpen R W) (vertexChartOpen_iSup_top R W)
    (vertexTwistPermLocalIso R ψ a b) (vertexTwistPermLocal_hom_compatible R ψ a b hb)
      (vertexTwistPermLocal_inv_compatible R ψ a b hb) τ

/-- **Frame compatibility.** On every chart, the transport followed by the chart frame of the
relabeled twist is the transported chart frame. -/
theorem vertexTwistPermIso_chart (τ : W → Fin 2) :
    (SheafOfModules.overFunctor (vertexScheme R W).ringCatSheaf (vertexChartOpen R W τ)).map
      (vertexTwistPermIso R ψ a b hb).hom ≫ (vertexTwistOverChartIso R W b τ).hom =
        (vertexTwistPermChartFrame R ψ a τ).hom := by
  rw [← Functor.mapIso_hom, vertexTwistPermIso_over]
  simp only [vertexTwistPermLocalIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- **Chart coefficients of the transport.** On every subopen of the chart of `τ`, the chart
coefficient of the transported section is the inverse structure map of the chart coefficient of
the original section over the preimage, in the chart of `τ ∘ ψ`. -/
theorem vertexTwistPermIso_chartCoefficient (τ : W → Fin 2) (U : (vertexScheme R W).Opens)
    (hU : U ≤ vertexChartOpen R W τ) (x : Γ(vertexTwistSheaf R V a, vertexSchemePerm R ψ.symm ⁻¹ᵁ U)) :
    vertexTwistSheafChartCoefficient R W b τ U hU ((vertexTwistPermIso R ψ a b hb).hom.app U x) =
      inv ((vertexSchemePerm R ψ.symm).app U)
        (vertexTwistSheafChartCoefficient R V a (fun v => τ (ψ v)) _
          (((vertexSchemePerm R ψ.symm).preimage_mono hU).trans
            (vertexSchemePerm_symm_preimage_chartOpen R ψ τ).le) x) := by
  have h := congrArg (fun f => (f.val.app (op (Over.mk (homOfLE hU)))).hom x)
    (vertexTwistPermIso_chart R ψ a b hb τ)
  exact h

/-- The underlying abelian sheaf of the pushforward is the transported abelian sheaf. -/
theorem vertexSheafPerm_obj_toSheaf (M : (vertexScheme R V).Modules) :
    (vertexSheafPerm R ψ).functor.obj ((SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).obj M) =
      (SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).obj
        ((Scheme.Modules.pushforward (vertexSchemePerm R ψ.symm)).obj M) := rfl

/-- **Transport of the abelian multi-twist.** The image of `O(a)` under the equivalence of
abelian sheaf categories `vertexSheafPerm R ψ` is `O(b)` whenever `b ∘ ψ = a`. -/
noncomputable def vertexTwistAbelianPermIso :
    (vertexSheafPerm R ψ).functor.obj (vertexTwistAbelianSheaf R V a) ≅
      vertexTwistAbelianSheaf R W b :=
  (SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).mapIso (vertexTwistPermIso R ψ a b hb)

/-- The abelian transport is the underlying morphism of the module transport. -/
theorem vertexTwistAbelianPermIso_hom :
    (vertexTwistAbelianPermIso R ψ a b hb).hom =
      (SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map (vertexTwistPermIso R ψ a b hb).hom :=
  rfl

/-- The transport of `O(a)` to the twist `a ∘ ψ⁻¹`. -/
noncomputable def vertexTwistAbelianPermIsoSymm :
    (vertexSheafPerm R ψ).functor.obj (vertexTwistAbelianSheaf R V a) ≅
      vertexTwistAbelianSheaf R W (fun w => a (ψ.symm w)) :=
  vertexTwistAbelianPermIso R ψ a (fun w => a (ψ.symm w)) (fun v => by simp)

end BPFixedPoints.Multigraph
