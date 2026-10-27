import BPFixedPoints.Incidence.VertexMapPullbackCohomology
import BPFixedPoints.Incidence.VertexPermutationTwistSheaf
import BPFixedPoints.Incidence.VertexProjectiveTwistPairChartComparison
import BPFixedPoints.Incidence.SchemeModulePullbackRestrictionFrames
import BPFixedPoints.Incidence.SchemeModuleLocalFramePullbackCoherence
import BPFixedPoints.Incidence.EdgeExteriorDegreeZero
import BPFixedPoints.Incidence.VertexProjectiveTwistCohomologyRanks
import BPFixedPoints.Incidence.CechProductPermutation

/-!
# Pullback of multi-twists and of the exterior bundle along the coordinate map of a vertex map

Let `f : V → W` be a function of finite vertex sets and `a_f : (P¹)^W → (P¹)^V` its coordinate map
(`vertexSchemeMap`). For a twist `a : V → ℤ` let `b w = Σ_{f v = w} a v`.

**The twist isomorphism.** On the chart of `τ : W → Fin 2` the map `a_f` factors through the chart
of `τ ∘ f` (`vertexChartMapLift`), and on pair intersections through the pair intersection of the
pulled-back charts (`vertexChartPairMapLift`). Pulling back the chart and pair frames of `O(a)`
along these lifts gives rank-one frames of `a_f^* O(a)` (`vertexTwistPullChartIso`,
`vertexTwistPullPairIso`); the chart frames restrict to the pair frames
(`vertexTwistPullChartIso_left`, `_right`). Their transition is the pullback of the transition unit
of `O(a)`, which is the transition unit of `O(b)` (`vertexTwistSheafPairUnit_pullback`: the factor
units of the vertices `v` with `f v = w` multiply to the factor unit of `w`, by
`twistSheafPairUnit_sum`). The chart comparisons therefore glue to an isomorphism of sheaves of
modules `vertexTwistPullbackIso : a_f^* O(a) ≅ O(b)` (`moduleFrameGlueIso`), which on every chart
is the pulled-back frame followed by the inverse frame of `O(b)` (`vertexTwistPullbackIso_chart`).
It is built from the actual morphism of schemes and Mathlib's pullback of sheaves of modules; no
exactness of that pullback is used, and nothing is defined through states.

**Cohomology.** Composing the pullback of Ext-defined cohomology `vertexModuleHPullback` (inverse
image of abelian sheaves and the comparison `a_f⁻¹ → a_f^*`) with this isomorphism gives the map of
multi-twist cohomology `vertexTwistHPullback : H^n((P¹)^V, O(a)) → H^n((P¹)^W, O(b))`. For
nonpositive twists `-d` with `d' w = Σ_{f v = w} d v`, the target is concentrated in degree
`cohomologyDegree d'`, so the map vanishes in every other degree
(`vertexTwistHPullback_eq_zero_of_ne`); in particular it vanishes in the degree
`cohomologyDegree d` of the source states whenever `f` identifies two vertices of the twist support
of `d` (`vertexTwistHPullback_eq_zero_of_not_injOn`).

**The exterior bundle.** For a vertex map `φ : VertexMap G H`, the degrees of `H` are the fibrewise
sums of those of `G` (`VertexMap.neg_deg_eq_sum_fiber`), so every exterior summand pulls back to the
exterior summand of `H` (`VertexMap.exteriorSummandPullbackIso`), the pullback of the exterior
bundle is the exterior bundle of `H` (`VertexMap.exteriorBundlePullbackIso`, using that the
pullback preserves finite biproducts), and `VertexMap.exteriorCohomologyPullback` is the map
`H^n((P¹)^V, ∧^q F_G^∨) → H^n((P¹)^W, ∧^q F_H^∨)`. Its component on the summand of an edge set `S`
is the multi-twist map of `S` (`VertexMap.exteriorCohomologyPullback_proj`), so it vanishes on the
summand of every edge set on whose support the vertex map collides, in the degree where that
summand has its states (`VertexMap.exteriorCohomologyPullback_proj_eq_zero_of_not_injOn`); this is
the geometric counterpart of the collision vanishing `incidenceTorMap_eq_zero_of_not_injOn`.

The state formula of these maps on non-colliding supports is `vertexMapTwistStateFormula`
(`VertexMapTwistStateFormula.lean`). Not proved: functoriality under composition, and agreement
with `vertexTwistHPerm` for vertex bijections.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace SheafTools
open ProjectiveLine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false

variable (R : Type) [CommRing R] {V W : Type} [Fintype V] [Fintype W] (f : V → W)

/-! ## Lifts of the coordinate map to the charts -/

/-- The coordinate map on the chart of `τ` factors through the chart of `τ ∘ f`. -/
noncomputable def vertexChartMapLift (τ : W → Fin 2) :
    (vertexChartOpen R W τ).toScheme ⟶ (vertexChartOpen R V (fun v => τ (f v))).toScheme :=
  IsOpenImmersion.lift (vertexChartOpen R V (fun v => τ (f v))).ι
    ((vertexChartOpen R W τ).ι ≫ vertexSchemeMap R f) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact vertexChartOpen_le_preimage R f τ x.2)

@[reassoc] theorem vertexChartMapLift_fac (τ : W → Fin 2) :
    vertexChartMapLift R f τ ≫ (vertexChartOpen R V (fun v => τ (f v))).ι =
      (vertexChartOpen R W τ).ι ≫ vertexSchemeMap R f :=
  IsOpenImmersion.lift_fac _ _ _

/-- The coordinate map on the pair intersection of the charts of `τ` and `τ'` factors through the
pair intersection of the charts of `τ ∘ f` and `τ' ∘ f`. -/
noncomputable def vertexChartPairMapLift (τ τ' : W → Fin 2) :
    (vertexChartPairOpen R W τ τ').toScheme ⟶
      (vertexChartPairOpen R V (fun v => τ (f v)) (fun v => τ' (f v))).toScheme :=
  IsOpenImmersion.lift (vertexChartPairOpen R V (fun v => τ (f v)) (fun v => τ' (f v))).ι
    ((vertexChartPairOpen R W τ τ').ι ≫ vertexSchemeMap R f) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact ⟨vertexChartOpen_le_preimage R f τ x.2.1, vertexChartOpen_le_preimage R f τ' x.2.2⟩)

@[reassoc] theorem vertexChartPairMapLift_fac (τ τ' : W → Fin 2) :
    vertexChartPairMapLift R f τ τ' ≫
        (vertexChartPairOpen R V (fun v => τ (f v)) (fun v => τ' (f v))).ι =
      (vertexChartPairOpen R W τ τ').ι ≫ vertexSchemeMap R f :=
  IsOpenImmersion.lift_fac _ _ _

/-- The pair lift followed by the projection lift of `v` is the projection lift of `f v`. -/
theorem vertexChartPairMapLift_projectionLift (τ τ' : W → Fin 2) (v : V) :
    vertexChartPairMapLift R f τ τ' ≫
        vertexChartPairProjectionLift R V (fun v => τ (f v)) (fun v => τ' (f v)) v =
      vertexChartPairProjectionLift R W τ τ' (f v) := by
  apply (cancel_mono (standardPairOpen R (τ (f v)) (τ' (f v))).ι).mp
  rw [Category.assoc, vertexChartPairProjectionLift_fac, vertexChartPairMapLift_fac_assoc,
    vertexSchemeMap_projection, vertexChartPairProjectionLift_fac]

/-! ## Transition units -/

/-- The pair transition unit of a finite sum of twists is the product of the units. -/
theorem twistSheafPairUnit_sum {ι : Type*} (s : Finset ι) (a : ι → ℤ) (i j : Fin 2) :
    twistSheafPairUnit R (∑ k ∈ s, a k) i j = ∏ k ∈ s, twistSheafPairUnit R (a k) i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [twistSheafPairUnit_zero]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.prod_insert hk, twistSheafPairUnit_add, ih]

variable [DecidableEq W]

/-- **The pulled-back transition unit is the transition unit of the pushed-forward twist**: with
`b w = Σ_{f v = w} a v`, the pair transition of `O(a)` on `(P¹)^V`, pulled back along the coordinate
map on the pair intersection of the charts `τ`, `τ'` of `W`, is the pair transition of `O(b)`. -/
theorem vertexTwistSheafPairUnit_pullback (a : V → ℤ) (b : W → ℤ)
    (hb : ∀ w, b w = ∑ v ∈ Finset.univ.filter (fun v => f v = w), a v) (τ τ' : W → Fin 2) :
    (vertexChartPairMapLift R f τ τ').appTop
        (vertexTwistSheafPairUnit R V a (fun v => τ (f v)) (fun v => τ' (f v)) :
          Γ((vertexChartPairOpen R V (fun v => τ (f v)) (fun v => τ' (f v))).toScheme, ⊤)) =
      (vertexTwistSheafPairUnit R W b τ τ' : Γ((vertexChartPairOpen R W τ τ').toScheme, ⊤)) := by
  simp only [vertexTwistSheafPairUnit, vertexTwistPairFactorUnit, Units.coe_prod, Units.coe_map,
    map_prod]
  have hl : ∀ v, (vertexChartPairMapLift R f τ τ').appTop
      ((vertexChartPairProjectionLift R V (fun v => τ (f v)) (fun v => τ' (f v)) v).appTop
        (twistSheafPairUnit R (a v) (τ (f v)) (τ' (f v)) :
          Γ((standardPairOpen R (τ (f v)) (τ' (f v))).toScheme, ⊤))) =
      (vertexChartPairProjectionLift R W τ τ' (f v)).appTop
        (twistSheafPairUnit R (a v) (τ (f v)) (τ' (f v)) :
          Γ((standardPairOpen R (τ (f v)) (τ' (f v))).toScheme, ⊤)) := by
    intro v
    rw [← vertexChartPairMapLift_projectionLift R f τ τ' v, Scheme.Hom.comp_appTop]
    rfl
  simp only [MonoidHom.coe_ofClass, RingHom.toMonoidHom_eq_coe] at hl ⊢
  rw [Finset.prod_congr rfl (fun v _ => hl v)]
  have hr : ∀ w, (vertexChartPairProjectionLift R W τ τ' w).appTop.hom
      (twistSheafPairUnit R (b w) (τ w) (τ' w) : Γ((standardPairOpen R (τ w) (τ' w)).toScheme, ⊤)) =
      ∏ v ∈ Finset.univ.filter (fun v => f v = w),
        (vertexChartPairProjectionLift R W τ τ' (f v)).appTop.hom
          (twistSheafPairUnit R (a v) (τ (f v)) (τ' (f v)) :
            Γ((standardPairOpen R (τ (f v)) (τ' (f v))).toScheme, ⊤)) := by
    intro w
    rw [hb w, twistSheafPairUnit_sum, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun v hv => ?_
    obtain ⟨-, hv⟩ := Finset.mem_filter.1 hv
    subst hv
    rfl
  rw [Finset.prod_congr rfl (fun w _ => hr w)]
  exact (Finset.prod_fiberwise Finset.univ f _).symm

/-! ## Pulled-back chart frames -/

variable (a : V → ℤ)

/-- The pullback of the multi-twist `O(a)` of `V` along the coordinate map `a_f`. -/
noncomputable abbrev vertexTwistPullback : (vertexScheme R W).Modules :=
  (Scheme.Modules.pullback (vertexSchemeMap R f)).obj (vertexTwistSheaf R V a)

/-- The chart frame of `O(a)` on the chart of `τ ∘ f`, pulled back to the chart of `τ`. -/
noncomputable def vertexTwistPullChartIso (τ : W → Fin 2) :
    (vertexTwistPullback R f a).restrict (vertexChartOpen R W τ).ι ≅
      SheafOfModules.unit (vertexChartOpen R W τ).toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback (vertexChartOpen R W τ).ι).app _ ≪≫
    (Scheme.Modules.pullbackComp (vertexChartOpen R W τ).ι (vertexSchemeMap R f)).app _ ≪≫
      modulePullbackLocalUnitIso _ (vertexChartOpen R V (fun v => τ (f v))) (vertexTwistSheaf R V a)
        (vertexTwistSheafChartIso R V a (fun v => τ (f v))) (vertexChartMapLift R f τ)
        (vertexChartMapLift_fac R f τ)

/-- The pair frame of `O(a)` on the pair intersection of the charts of `τ ∘ f`, `τ' ∘ f`, pulled
back to the pair intersection of the charts of `τ`, `τ'`. -/
noncomputable def vertexTwistPullPairIso (τ τ' : W → Fin 2) (right : Bool) :
    (vertexTwistPullback R f a).restrict (vertexChartPairOpen R W τ τ').ι ≅
      SheafOfModules.unit (vertexChartPairOpen R W τ τ').toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback (vertexChartPairOpen R W τ τ').ι).app _ ≪≫
    (Scheme.Modules.pullbackComp (vertexChartPairOpen R W τ τ').ι (vertexSchemeMap R f)).app _ ≪≫
      modulePullbackLocalUnitIso _ (vertexChartPairOpen R V (fun v => τ (f v)) (fun v => τ' (f v)))
        (vertexTwistSheaf R V a)
        (vertexTwistSheafPairIso R V a (fun v => τ (f v)) (fun v => τ' (f v)) right)
        (vertexChartPairMapLift R f τ τ') (vertexChartPairMapLift_fac R f τ τ')

/-- The pair lift refines the left chart lift. -/
theorem vertexChartPairMapLift_left (τ τ' : W → Fin 2) :
    vertexChartPairMapLift R f τ τ' ≫ (vertexScheme R V).homOfLE
        (show vertexChartPairOpen R V (fun v => τ (f v)) (fun v => τ' (f v)) ≤
          vertexChartOpen R V (fun v => τ (f v)) from inf_le_left) =
      (vertexScheme R W).homOfLE (show vertexChartPairOpen R W τ τ' ≤ vertexChartOpen R W τ from
        inf_le_left) ≫ vertexChartMapLift R f τ := by
  apply (cancel_mono (vertexChartOpen R V (fun v => τ (f v))).ι).mp
  rw [Category.assoc, Scheme.homOfLE_ι, vertexChartPairMapLift_fac, Category.assoc,
    vertexChartMapLift_fac, ← Category.assoc, Scheme.homOfLE_ι]

/-- The pair lift refines the right chart lift. -/
theorem vertexChartPairMapLift_right (τ τ' : W → Fin 2) :
    vertexChartPairMapLift R f τ τ' ≫ (vertexScheme R V).homOfLE
        (show vertexChartPairOpen R V (fun v => τ (f v)) (fun v => τ' (f v)) ≤
          vertexChartOpen R V (fun v => τ' (f v)) from inf_le_right) =
      (vertexScheme R W).homOfLE (show vertexChartPairOpen R W τ τ' ≤ vertexChartOpen R W τ' from
        inf_le_right) ≫ vertexChartMapLift R f τ' := by
  apply (cancel_mono (vertexChartOpen R V (fun v => τ' (f v))).ι).mp
  rw [Category.assoc, Scheme.homOfLE_ι, vertexChartPairMapLift_fac, Category.assoc,
    vertexChartMapLift_fac, ← Category.assoc, Scheme.homOfLE_ι]

/-- The pulled-back left chart frame restricts to the pulled-back left pair frame. -/
theorem vertexTwistPullChartIso_left (τ τ' : W → Fin 2) :
    moduleLocalFrameRestriction (vertexScheme R W)
        (homOfLE (show vertexChartPairOpen R W τ τ' ≤ vertexChartOpen R W τ from inf_le_left))
        (vertexTwistPullback R f a) (vertexTwistPullChartIso R f a τ) =
      vertexTwistPullPairIso R f a τ τ' false := by
  rw [vertexTwistPullChartIso, moduleLocalFrameRestriction_pullbackLocalFrame,
    vertexTwistPullPairIso, ← vertexTwistSheafChartFrameRestriction_left_pair]
  congr 2
  exact modulePullbackLocalUnitIso_refine_fac
    (homOfLE (show vertexChartPairOpen R V (fun v => τ (f v)) (fun v => τ' (f v)) ≤
      vertexChartOpen R V (fun v => τ (f v)) from inf_le_left)) _ _ _ _ _ _
    (vertexChartPairMapLift_fac R f τ τ') (vertexChartPairMapLift_left R f τ τ')

/-- The pulled-back right chart frame restricts to the pulled-back right pair frame. -/
theorem vertexTwistPullChartIso_right (τ τ' : W → Fin 2) :
    moduleLocalFrameRestriction (vertexScheme R W)
        (homOfLE (show vertexChartPairOpen R W τ τ' ≤ vertexChartOpen R W τ' from inf_le_right))
        (vertexTwistPullback R f a) (vertexTwistPullChartIso R f a τ') =
      vertexTwistPullPairIso R f a τ τ' true := by
  rw [vertexTwistPullChartIso, moduleLocalFrameRestriction_pullbackLocalFrame,
    vertexTwistPullPairIso, ← vertexTwistSheafChartFrameRestriction_right_pair]
  congr 2
  exact modulePullbackLocalUnitIso_refine_fac
    (homOfLE (show vertexChartPairOpen R V (fun v => τ (f v)) (fun v => τ' (f v)) ≤
      vertexChartOpen R V (fun v => τ' (f v)) from inf_le_right)) _ _ _ _ _ _
    (vertexChartPairMapLift_fac R f τ τ') (vertexChartPairMapLift_right R f τ τ')

variable (b : W → ℤ) (hb : ∀ w, b w = ∑ v ∈ Finset.univ.filter (fun v => f v = w), a v)

include hb in
/-- **The pulled-back pair frames have the transition of `O(b)`.** -/
theorem vertexTwistPullPairIso_transition (τ τ' : W → Fin 2) :
    (vertexTwistPullPairIso R f a τ τ' false).hom =
      (vertexTwistPullPairIso R f a τ τ' true).hom ≫
        unitGlobalMultiplication (vertexChartPairOpen R W τ τ').toScheme
          (vertexTwistSheafPairUnit R W b τ τ' :
            Γ((vertexChartPairOpen R W τ τ').toScheme, ⊤)) := by
  have h := modulePullbackLocalUnitIso_transition _
    (vertexChartPairOpen R V (fun v => τ (f v)) (fun v => τ' (f v))) (vertexTwistSheaf R V a)
    (vertexTwistSheafPairIso R V a (fun v => τ (f v)) (fun v => τ' (f v)) false)
    (vertexTwistSheafPairIso R V a (fun v => τ (f v)) (fun v => τ' (f v)) true)
    (vertexChartPairMapLift R f τ τ') (vertexChartPairMapLift_fac R f τ τ') _
    (vertexTwistSheafPairIso_transition R V a (fun v => τ (f v)) (fun v => τ' (f v)))
  rw [vertexTwistSheafPairUnit_pullback R f a b hb τ τ'] at h
  simp only [vertexTwistPullPairIso, Iso.trans_hom, Category.assoc, h]

/-! ## Over-site frames and gluing -/

/-- The pulled-back chart frame in the native over-site. -/
noncomputable def vertexTwistPullOverChartIso (τ : W → Fin 2) :
    (vertexTwistPullback R f a).over (vertexChartOpen R W τ) ≅
      SheafOfModules.unit ((vertexScheme R W).ringCatSheaf.over (vertexChartOpen R W τ)) :=
  moduleOverUnitIso (vertexScheme R W) (vertexTwistPullback R f a) (vertexChartOpen R W τ)
    (vertexTwistPullChartIso R f a τ)

/-- The pulled-back pair frame in the native over-site. -/
noncomputable def vertexTwistPullOverPairIso (τ τ' : W → Fin 2) (right : Bool) :
    (vertexTwistPullback R f a).over (vertexChartPairOpen R W τ τ') ≅
      SheafOfModules.unit ((vertexScheme R W).ringCatSheaf.over (vertexChartPairOpen R W τ τ')) :=
  moduleOverUnitIso (vertexScheme R W) (vertexTwistPullback R f a) (vertexChartPairOpen R W τ τ')
    (vertexTwistPullPairIso R f a τ τ' right)

theorem vertexTwistPullOverChartIso_left (τ τ' : W → Fin 2) :
    moduleOverFrameRestriction (vertexScheme R W)
        (homOfLE (show vertexChartPairOpen R W τ τ' ≤ vertexChartOpen R W τ from inf_le_left))
        (vertexTwistPullback R f a) (vertexTwistPullOverChartIso R f a τ) =
      vertexTwistPullOverPairIso R f a τ τ' false := by
  rw [vertexTwistPullOverPairIso, ← vertexTwistPullChartIso_left, moduleLocalFrameRestriction,
    moduleOverUnitIso_moduleLocalFrameOfOver]
  rfl

theorem vertexTwistPullOverChartIso_right (τ τ' : W → Fin 2) :
    moduleOverFrameRestriction (vertexScheme R W)
        (homOfLE (show vertexChartPairOpen R W τ τ' ≤ vertexChartOpen R W τ' from inf_le_right))
        (vertexTwistPullback R f a) (vertexTwistPullOverChartIso R f a τ') =
      vertexTwistPullOverPairIso R f a τ τ' true := by
  rw [vertexTwistPullOverPairIso, ← vertexTwistPullChartIso_right, moduleLocalFrameRestriction,
    moduleOverUnitIso_moduleLocalFrameOfOver]
  rfl

include hb in
theorem vertexTwistPullOverPairIso_transition (τ τ' : W → Fin 2) :
    (vertexTwistPullOverPairIso R f a τ τ' false).hom =
      (vertexTwistPullOverPairIso R f a τ τ' true).hom ≫
        moduleOverMultiplication (vertexScheme R W) (vertexChartPairOpen R W τ τ')
          (vertexTwistSheafPairUnit R W b τ τ' : Γ((vertexChartPairOpen R W τ τ').toScheme, ⊤)) :=
  moduleOverUnitIso_transition _ _ _ _ _ _ (vertexTwistPullPairIso_transition R f a b hb τ τ')

/-- The chart comparison: the pulled-back chart frame followed by the inverse chart frame of
`O(b)`. -/
noncomputable def vertexTwistPullLocalIso (τ : W → Fin 2) :
    (vertexTwistPullback R f a).over (vertexChartOpen R W τ) ≅
      (vertexTwistSheaf R W b).over (vertexChartOpen R W τ) :=
  vertexTwistPullOverChartIso R f a τ ≪≫ (vertexTwistOverChartIso R W b τ).symm

include hb in
theorem vertexTwistPullLocal_hom_compatible :
    TopCat.Presheaf.IsCompatible (X := TopCat.of (vertexScheme R W))
      (moduleHomSheaf (vertexScheme R W) (vertexTwistPullback R f a)
        (vertexTwistSheaf R W b)).obj (vertexChartOpen R W)
      (fun τ => moduleOverHomSection (vertexScheme R W) _ _ (vertexChartOpen R W τ)
        (vertexTwistPullLocalIso R f a b τ).hom) := by
  intro τ τ'
  dsimp only [vertexTwistPullLocalIso, Iso.trans_hom, Iso.symm_hom]
  rw [moduleFrameMap_section_restrict, moduleFrameMap_section_restrict]
  have hL : Opens.infLELeft (vertexChartOpen R W τ) (vertexChartOpen R W τ') =
      homOfLE (show vertexChartPairOpen R W τ τ' ≤ vertexChartOpen R W τ from inf_le_left) :=
    Subsingleton.elim _ _
  have hR : Opens.infLERight (vertexChartOpen R W τ) (vertexChartOpen R W τ') =
      homOfLE (show vertexChartPairOpen R W τ τ' ≤ vertexChartOpen R W τ' from inf_le_right) :=
    Subsingleton.elim _ _
  rw [hL, hR, vertexTwistPullOverChartIso_left, vertexTwistPullOverChartIso_right,
    vertexTwistOverChartIso_left, vertexTwistOverChartIso_right]
  congr 1
  exact moduleFrameMap_eq_of_transition (vertexScheme R W)
    (vertexTwistPullOverPairIso R f a τ τ' false) (vertexTwistPullOverPairIso R f a τ τ' true)
    (vertexTwistOverPairIso R W b τ τ' false) (vertexTwistOverPairIso R W b τ τ' true) _
    (vertexTwistPullOverPairIso_transition R f a b hb τ τ')
    (vertexTwistOverPairIso_transition R W b τ τ')

include hb in
theorem vertexTwistPullLocal_inv_compatible :
    TopCat.Presheaf.IsCompatible (X := TopCat.of (vertexScheme R W))
      (moduleHomSheaf (vertexScheme R W) (vertexTwistSheaf R W b)
        (vertexTwistPullback R f a)).obj (vertexChartOpen R W)
      (fun τ => moduleOverHomSection (vertexScheme R W) _ _ (vertexChartOpen R W τ)
        (vertexTwistPullLocalIso R f a b τ).inv) := by
  intro τ τ'
  dsimp only [vertexTwistPullLocalIso, Iso.trans_inv, Iso.symm_inv]
  rw [moduleFrameMap_section_restrict, moduleFrameMap_section_restrict]
  have hL : Opens.infLELeft (vertexChartOpen R W τ) (vertexChartOpen R W τ') =
      homOfLE (show vertexChartPairOpen R W τ τ' ≤ vertexChartOpen R W τ from inf_le_left) :=
    Subsingleton.elim _ _
  have hR : Opens.infLERight (vertexChartOpen R W τ) (vertexChartOpen R W τ') =
      homOfLE (show vertexChartPairOpen R W τ τ' ≤ vertexChartOpen R W τ' from inf_le_right) :=
    Subsingleton.elim _ _
  rw [hL, hR, vertexTwistPullOverChartIso_left, vertexTwistPullOverChartIso_right,
    vertexTwistOverChartIso_left, vertexTwistOverChartIso_right]
  congr 1
  exact moduleFrameMap_eq_of_transition (vertexScheme R W)
    (vertexTwistOverPairIso R W b τ τ' false) (vertexTwistOverPairIso R W b τ τ' true)
    (vertexTwistPullOverPairIso R f a τ τ' false) (vertexTwistPullOverPairIso R f a τ τ' true) _
    (vertexTwistOverPairIso_transition R W b τ τ')
    (vertexTwistPullOverPairIso_transition R f a b hb τ τ')

/-- **The pullback of a multi-twist along the coordinate map of a vertex function**:
`a_f^* O(a) ≅ O(b)` with `b w = Σ_{f v = w} a v`, glued from the pulled-back chart frames. -/
noncomputable def vertexTwistPullbackIso : vertexTwistPullback R f a ≅ vertexTwistSheaf R W b :=
  moduleFrameGlueIso (vertexScheme R W) _ _ (vertexChartOpen R W) (vertexChartOpen_iSup_top R W)
    (vertexTwistPullLocalIso R f a b) (vertexTwistPullLocal_hom_compatible R f a b hb)
      (vertexTwistPullLocal_inv_compatible R f a b hb)

/-- The pullback isomorphism restricts on every chart to the specified chart comparison. -/
theorem vertexTwistPullbackIso_over (τ : W → Fin 2) :
    (SheafOfModules.overFunctor (vertexScheme R W).ringCatSheaf (vertexChartOpen R W τ)).mapIso
      (vertexTwistPullbackIso R f a b hb) = vertexTwistPullLocalIso R f a b τ :=
  moduleFrameGlueIso_over (vertexScheme R W) _ _ (vertexChartOpen R W)
    (vertexChartOpen_iSup_top R W)
    (vertexTwistPullLocalIso R f a b) (vertexTwistPullLocal_hom_compatible R f a b hb)
      (vertexTwistPullLocal_inv_compatible R f a b hb) τ

/-- **Frame compatibility.** On every chart of `W`, the pullback isomorphism followed by the chart
frame of `O(b)` is the pulled-back chart frame of `O(a)`. -/
theorem vertexTwistPullbackIso_chart (τ : W → Fin 2) :
    (SheafOfModules.overFunctor (vertexScheme R W).ringCatSheaf (vertexChartOpen R W τ)).map
      (vertexTwistPullbackIso R f a b hb).hom ≫ (vertexTwistOverChartIso R W b τ).hom =
        (vertexTwistPullOverChartIso R f a τ).hom := by
  rw [← Functor.mapIso_hom, vertexTwistPullbackIso_over]
  simp only [vertexTwistPullLocalIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-! ## The map of multi-twist cohomology -/

noncomputable local instance vertexTwistPullbackHasExt (S : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- **The pullback of multi-twist cohomology along the coordinate map** `a_f : (P¹)^W → (P¹)^V`:
`H^n((P¹)^V, O(a)) → H^n((P¹)^W, O(b))` with `b w = Σ_{f v = w} a v`. It is the pullback of
Ext-defined cohomology along the inverse image of abelian sheaves and the comparison
`a_f⁻¹ → a_f^*` (`vertexModuleHPullback`), followed by `a_f^* O(a) ≅ O(b)`
(`vertexTwistPullbackIso`). -/
noncomputable def vertexTwistHPullback (n : ℕ) :
    Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) n →+
      Sheaf.H.{1} (vertexTwistAbelianSheaf R W b) n :=
  (Sheaf.H.map ((SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
      (vertexTwistPullbackIso R f a b hb).hom) n).comp
    (vertexModuleHPullback R f (vertexTwistSheaf R V a) n)

theorem vertexTwistHPullback_apply (n : ℕ) (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) n) :
    vertexTwistHPullback R f a b hb n x =
      Sheaf.H.map ((SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
        (vertexTwistPullbackIso R f a b hb).hom) n
          (vertexModuleHPullback R f (vertexTwistSheaf R V a) n x) :=
  rfl

end BPFixedPoints.Multigraph

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace SheafTools
open ProjectiveLine CechProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false

noncomputable local instance vertexTwistPullbackHasExt' (S : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-! ## Concentration: vanishing on colliding supports -/

section Concentration

variable (R : Type) [CommRing R] [IsNoetherianRing R] {V W : Type} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W] (f : V → W)

/-- The twist support of a pushed-forward nonnegative twist is the image of the twist support. -/
theorem twistSupport_pushforward (d : V → ℕ) (d' : W → ℕ)
    (hd : ∀ w, d' w = ∑ v ∈ Finset.univ.filter (fun v => f v = w), d v) :
    twistSupport d' = (twistSupport d).image f := by
  ext w
  rw [mem_twistSupport, Finset.mem_image, hd w, Ne, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_twistSupport, not_forall]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, h, hv⟩
  · rintro ⟨v, h, hv⟩
    exact ⟨v, hv, h⟩

/-- **Concentration.** The pullback of multi-twist cohomology vanishes in every degree other than
the cohomological degree of the target twist. -/
theorem vertexTwistHPullback_eq_zero_of_ne (d : V → ℕ) (d' : W → ℕ)
    (hd : ∀ w, -(d' w : ℤ) = ∑ v ∈ Finset.univ.filter (fun v => f v = w), -(d v : ℤ))
    (n : ℕ) (hn : cohomologyDegree d' ≠ n)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n) :
    vertexTwistHPullback R f (fun v => -(d v : ℤ)) (fun w => -(d' w : ℤ)) hd n x = 0 :=
  vertexTwistCohomology_eq_zero_off_degree R W d' n hn _

/-- **Vanishing on colliding supports.** If `f` identifies two vertices of the twist support of
`d`, the pullback of multi-twist cohomology vanishes in the degree `cohomologyDegree d`, where the
cohomology of `O(-d)` is concentrated. -/
theorem vertexTwistHPullback_eq_zero_of_not_injOn (d : V → ℕ) (d' : W → ℕ)
    (hd' : ∀ w, d' w = ∑ v ∈ Finset.univ.filter (fun v => f v = w), d v)
    (hd : ∀ w, -(d' w : ℤ) = ∑ v ∈ Finset.univ.filter (fun v => f v = w), -(d v : ℤ))
    (h : ¬ Set.InjOn f (twistSupport d))
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) (cohomologyDegree d)) :
    vertexTwistHPullback R f (fun v => -(d v : ℤ)) (fun w => -(d' w : ℤ)) hd
        (cohomologyDegree d) x =
      0 := by
  apply vertexTwistHPullback_eq_zero_of_ne
  rw [cohomologyDegree_eq_card_twistSupport, cohomologyDegree_eq_card_twistSupport,
    twistSupport_pushforward f d d' hd']
  exact ne_of_lt (lt_of_le_of_ne Finset.card_image_le fun heq => h (Finset.card_image_iff.mp heq))

end Concentration

/-! ## The exterior bundle -/

section Exterior

variable (R : Type) [CommRing R] {V W E : Type} [Fintype V] [Fintype W] [DecidableEq V]
  [DecidableEq W] [LinearOrder E] [Fintype E] {G : Multigraph V E} {H : Multigraph W E}
  (φ : VertexMap G H)

/-- Minus the degrees of `H` are the fibrewise sums of minus the degrees of `G`. -/
theorem VertexMap.neg_deg_eq_sum_fiber (S : Finset E) (w : W) :
    -(H.deg S w : ℤ) = ∑ v ∈ Finset.univ.filter (fun v => φ.vertex v = w), -(G.deg S v : ℤ) := by
  rw [φ.deg_eq_sum_fiber, Finset.sum_neg_distrib, Nat.cast_sum]
  rfl

/-- The pullback of an exterior summand of `G` along `a_φ` is the exterior summand of `H`. -/
noncomputable def VertexMap.exteriorSummandPullbackIso (S : Finset E) :
    (Scheme.Modules.pullback (φ.schemeMap R)).obj (G.exteriorSummand R S) ≅ H.exteriorSummand R S :=
  vertexTwistPullbackIso R φ.vertex (fun v => -(G.deg S v : ℤ)) (fun w => -(H.deg S w : ℤ))
    (φ.neg_deg_eq_sum_fiber S)

/-- Finite products of sheaves of modules on a scheme. -/
local instance schemeModulesHasFiniteProducts (X : Scheme.{0}) : HasFiniteProducts X.Modules :=
  inferInstanceAs (HasFiniteProducts (SheafOfModules X.ringCatSheaf))

/-- Finite biproducts of sheaves of modules on a scheme. -/
local instance schemeModulesHasFiniteBiproducts (X : Scheme.{0}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The exterior summands of `G` in degree `q`, as a family of sheaves of modules. -/
noncomputable def exteriorSummandFamily (G : Multigraph V E) (q : ℕ) :
    Set.powersetCard E q → (vertexScheme R V).Modules :=
  fun S => G.exteriorSummand R S

/-- **The pullback of the exterior bundle** of `G` along `a_φ` is the exterior bundle of `H`,
summand by summand: the pullback preserves finite biproducts, and each summand is pulled back by
`exteriorSummandPullbackIso`. -/
noncomputable def VertexMap.exteriorBundlePullbackIso (q : ℕ) :
    (Scheme.Modules.pullback (φ.schemeMap R)).obj (G.exteriorBundle R q) ≅ H.exteriorBundle R q :=
  (Scheme.Modules.pullback (φ.schemeMap R)).mapBiproduct (exteriorSummandFamily R G q) ≪≫
    biproduct.mapIso (g := exteriorSummandFamily R H q) (fun S => φ.exteriorSummandPullbackIso R S)

/-- **The pullback of exterior cohomology along the coordinate map of a vertex map**:
`H^n((P¹)^V, ∧^q F_G^∨) → H^n((P¹)^W, ∧^q F_H^∨)`, from the actual morphism of schemes `a_φ`. -/
noncomputable def VertexMap.exteriorCohomologyPullback (q n : ℕ) :
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) n →+ Sheaf.H.{1} (H.exteriorBundleAbelian R q) n :=
  (Sheaf.H.map ((SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
      (φ.exteriorBundlePullbackIso R q).hom) n).comp (exteriorBundleHPullback R φ q n)

/-- The pullback of the exterior bundle is compatible with the summand projections. -/
theorem VertexMap.exteriorBundlePullbackIso_hom_π (q : ℕ) (S : Set.powersetCard E q) :
    (φ.exteriorBundlePullbackIso R q).hom ≫ biproduct.π (exteriorSummandFamily R H q) S =
      (Scheme.Modules.pullback (φ.schemeMap R)).map (biproduct.π (exteriorSummandFamily R G q) S) ≫
        (φ.exteriorSummandPullbackIso R S).hom := by
  simp only [VertexMap.exteriorBundlePullbackIso, Iso.trans_hom, Category.assoc,
    biproduct.mapIso_hom, biproduct.map_π, Functor.mapBiproduct_hom]
  erw [biproduct.lift_π_assoc]

/-- **Summand components.** The `S`-component of the pullback of exterior cohomology is the
pullback of the cohomology of the summand of `S`. -/
theorem VertexMap.exteriorCohomologyPullback_proj (q n : ℕ) (S : Set.powersetCard E q)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) n) :
    Sheaf.H.map (H.exteriorProj R q S) n (φ.exteriorCohomologyPullback R q n x) =
      vertexTwistHPullback R φ.vertex (fun v => -(G.deg S v : ℤ)) (fun w => -(H.deg S w : ℤ))
        (φ.neg_deg_eq_sum_fiber S) n (Sheaf.H.map (G.exteriorProj R q S) n x) := by
  have hcomp : (SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
        (φ.exteriorBundlePullbackIso R q).hom ≫ H.exteriorProj R q S =
      (SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
          ((Scheme.Modules.pullback (φ.schemeMap R)).map
            (biproduct.π (exteriorSummandFamily R G q) S)) ≫
        (SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
          (φ.exteriorSummandPullbackIso R S).hom := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ (φ.exteriorBundlePullbackIso_hom_π R q S)
  calc Sheaf.H.map (H.exteriorProj R q S) n (φ.exteriorCohomologyPullback R q n x)
      = Sheaf.H.map ((SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
          (φ.exteriorBundlePullbackIso R q).hom ≫ H.exteriorProj R q S) n
            (exteriorBundleHPullback R φ q n x) := (Sheaf.H.map_comp_apply _ _ _).symm
    _ = Sheaf.H.map ((SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
          ((Scheme.Modules.pullback (φ.schemeMap R)).map
            (biproduct.π (exteriorSummandFamily R G q) S)) ≫
        (SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
          (φ.exteriorSummandPullbackIso R S).hom) n (exteriorBundleHPullback R φ q n x) :=
        congrArg (fun g => Sheaf.H.map g n (exteriorBundleHPullback R φ q n x)) hcomp
    _ = Sheaf.H.map ((SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
          (φ.exteriorSummandPullbackIso R S).hom) n
          (Sheaf.H.map ((SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
            ((Scheme.Modules.pullback (φ.schemeMap R)).map
              (biproduct.π (exteriorSummandFamily R G q) S))) n
            (exteriorBundleHPullback R φ q n x)) := Sheaf.H.map_comp_apply _ _ _
    _ = Sheaf.H.map ((SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
          (φ.exteriorSummandPullbackIso R S).hom) n
          (moduleSheafHPullback (φ.schemeMap R) (G.exteriorSummand R S) n
            (Sheaf.H.map (G.exteriorProj R q S) n x)) :=
        congrArg (fun y => Sheaf.H.map ((SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
          (φ.exteriorSummandPullbackIso R S).hom) n y)
          (moduleSheafHPullback_map (φ.schemeMap R) (biproduct.π (exteriorSummandFamily R G q) S) n
            x).symm
    _ = _ := rfl

/-- **Vanishing on colliding edge sets.** If the vertex map identifies two vertices of the support
of the edge set `S`, the `S`-component of the pullback of exterior cohomology vanishes in the degree
`cohomologyDegree (G.deg S)`, the only degree in which the summand of `S` has cohomology. -/
theorem VertexMap.exteriorCohomologyPullback_proj_eq_zero_of_not_injOn [IsNoetherianRing R]
    (q : ℕ) (S : Set.powersetCard E q) (h : ¬ Set.InjOn φ.vertex (G.support S))
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) (cohomologyDegree (G.deg S))) :
    Sheaf.H.map (H.exteriorProj R q S) _ (φ.exteriorCohomologyPullback R q _ x) = 0 := by
  rw [φ.exteriorCohomologyPullback_proj R]
  have hs : twistSupport (G.deg S) = G.support S := by
    ext v
    rw [mem_twistSupport, mem_support_iff, Nat.pos_iff_ne_zero]
  exact vertexTwistHPullback_eq_zero_of_not_injOn (R := R) (f := φ.vertex) (d := G.deg S)
    (d' := H.deg S) (fun w => φ.deg_eq_sum_fiber S w) (φ.neg_deg_eq_sum_fiber S) (hs ▸ h) _

end Exterior

end BPFixedPoints.Multigraph
