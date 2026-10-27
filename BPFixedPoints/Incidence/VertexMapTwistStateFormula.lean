import BPFixedPoints.Incidence.VertexMapTwistStateCoefficients
import BPFixedPoints.Incidence.VertexMapPullbackExterior
import BPFixedPoints.Incidence.BinaryCoverRefinementVertex

/-!
# The multi-twist state formula for vertex maps

For a function `f : V → W` of finite vertex sets (vertices may be identified, and vertices of `W`
may be missed), `vertexTwistHPullback` is the map of multi-twist cohomology
`H^n((P¹)^V, O(-d)) → H^n((P¹)^W, O(-d'))` along the coordinate map `a_f`, with `d'` the
fibrewise sum of `d` (`VertexMapPullbackTwist`). It is defined from the actual morphism of schemes,
the inverse image of abelian sheaves, the comparison `a_f⁻¹ → a_f^*` and the glued twist
isomorphism; states are used only in the proofs below.

**Class transport.** For a binary cover `U'` of `(P¹)^V` and its preimage cover `U` of `(P¹)^W`,
`vertexTwistHPullback` sends the class of a cubical cocycle of `U'` to the class of the pulled
back cocycle `vertexTwistPullCycles` (`vertexTwistHPullback_cellClass`, from `cellPull_class`), whose
face sections are the pulled back twist sections of the face sections
(`sectionsEquiv_vertexTwistPullCycles`).

**Injective maps.** For injective `j`, the preimage of the standard cover of `(P¹)^V` is the
standard cover of `(P¹)^W` relabelled along `j`; relabelling along the forgetful chain map
(`relabel_cocycleComparison`) and the face coordinates of pulled back twist sections
(`vertexTwistPullSection_faceSections`) show that the coefficient chain of the image of the
canonical representative is `cechExtend` of the coefficient chain, whence
`vertexTwistActualStateAt_pullback_of_injective`.

**Arbitrary maps.** Let `A` be the twist support of `d`; `f` is injective on `A` when
`d' (f v) = d v` on `A` (`injOn_twistSupport`). Every class of `O(-d)` is the pullback along the
coordinate projection to `(P¹)^A` of a class with the restricted states (`supportStates`), by the
injective case. Its pullback along `a_f` is computed through the `A`-indexed cover of `(P¹)^V`,
whose preimage under `a_f` is the standard cover of `(P¹)^W` relabelled along the injective map
`f ∘ (A ↪ V)`; the face coordinates compose (`facePull_comp`) and the Koszul signs compose
(`vertexMapSign_comp`). This proves, unconditionally:
* **`vertexMapTwistStateFormula : VertexMapTwistStateFormula R f`**, in every degree;
* the exterior state formula `VertexMap.exteriorCohomologyState_pullback`;
* the naturality square `VertexMap.incidenceTorExteriorEquiv_vertexMap` of
  `incidenceTorExteriorEquiv` for vertex maps that may identify vertices.

Not proved here: functoriality of `sheafHPullback` under composition of maps (it is not needed),
and compatibility of the geometric map with the exterior products.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
open Opposite SheafTools SheafTools.BinaryCells ExtResolutionTools ProjectiveLine CechProduct Finsupp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false

noncomputable local instance vertexMapTwistStateHasExt (S : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) := HasExt.standard _

/-- Two composites of restrictions between the same opens agree. -/
theorem modulePresheaf_map_map_eq {Z : Scheme.{0}} (N : Z.Modules) {A B B' C : Z.Opens}
    (m₁ : op A ⟶ op B) (m₂ : op B ⟶ op C) (m₃ : op A ⟶ op B') (m₄ : op B' ⟶ op C)
    (x : Γ(N, A)) :
    N.presheaf.map m₂ (N.presheaf.map m₁ x) = N.presheaf.map m₄ (N.presheaf.map m₃ x) := by
  rw [modulePresheaf_map_map N m₁ m₂ (m₁ ≫ m₂), modulePresheaf_map_map N m₃ m₄ (m₁ ≫ m₂)]

section Transport

variable (R : Type) [CommRing R] {V W : Type} [Fintype V] [Fintype W] [DecidableEq V]
  [DecidableEq W] (f : V → W) (a : V → ℤ) (b : W → ℤ)
  (hb : ∀ w, b w = ∑ v ∈ Finset.univ.filter (fun v => f v = w), a v)
  {I : Type} [Fintype I] [DecidableEq I] (U' : I → Fin 2 → (vertexScheme R V).Opens)
  (U : I → Fin 2 → (vertexScheme R W).Opens)
  (hU : ∀ i c, (Opens.map (vertexSchemeMap R f).base).obj (U' i c) = U i c)

/-- The abelian comparison map after the inverse image: the comparison `a_f⁻¹ → a_f^*` followed by
the twist isomorphism `a_f^* O(a) ≅ O(b)`. -/
noncomputable def vertexTwistPullComparison :
    (topSheafPullback (vertexSchemeMap R f).base).obj (vertexTwistAbelianSheaf R V a) ⟶
      vertexTwistAbelianSheaf R W b :=
  moduleSheafPullbackComparison (vertexSchemeMap R f) (vertexTwistSheaf R V a) ≫
    (SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
      (vertexTwistPullbackIso R f a b hb).hom

/-- **The pulled back cubical cocycle**: the comparison chain map along `a_f`, the inverse image of
the cocycle, and `vertexTwistPullComparison`. -/
noncomputable def vertexTwistPullCycles (n : ℕ)
    (z : (cubicalTower U').cycles (vertexTwistAbelianSheaf R V a) n) :
    (cubicalTower U).cycles (vertexTwistAbelianSheaf R W b) n :=
  (cubicalTower U).mapCycles (vertexTwistPullComparison R f a b hb) n
    ((complexMapSourceMap (topSheafPullback (vertexSchemeMap R f).base) (sheafComplex_exact U')
      (sheafComplex_exact U) (cellPullMap (vertexSchemeMap R f).base U U' hU)).cycles _ n
        (towerMapCycles (topSheafPullback (vertexSchemeMap R f).base) n z))

omit [DecidableEq V] in
/-- The pulled back cocycle is the composite of the comparison chain map, the inverse image of
the cocycle and the comparison of sheaves. -/
theorem vertexTwistPullCycles_val (n : ℕ)
    (z : (cubicalTower U').cycles (vertexTwistAbelianSheaf R V a) n) :
    (vertexTwistPullCycles R f a b hb U' U hU n z).val =
      cellPullComponent (vertexSchemeMap R f).base U U' hU n ≫
        (topSheafPullback (vertexSchemeMap R f).base).map z.val ≫
          vertexTwistPullComparison R f a b hb :=
  (Category.assoc _ _ _)

omit [DecidableEq V] in
/-- **The geometric map on cubical classes.** The pullback of multi-twist cohomology along `a_f`
sends the class of a cubical cocycle of a binary cover `U'` of `(P¹)^V` to the class of the pulled
back cocycle of the preimage cover `U` of `(P¹)^W`. -/
theorem vertexTwistHPullback_cellClass (hc' : (⊤ : (vertexScheme R V).Opens) ≤ ⨆ c, chartOpen U' c)
    (hc : (⊤ : (vertexScheme R W).Opens) ≤ ⨆ c, chartOpen U c) (n : ℕ)
    (z : (cubicalTower U').cycles (vertexTwistAbelianSheaf R V a) n) :
    letI := augmentation_epi U' hc'
    letI := augmentation_epi U hc
    vertexTwistHPullback R f a b hb n (localSheafTopEquiv _ n
        (augmentedComplexCocycleComparison (sheafComplex U') _ (sheafComplex_exact U')
          (augmentation U') (augmentation_zero U') (augmentation_exact U') n z)) =
      localSheafTopEquiv _ n
        (augmentedComplexCocycleComparison (sheafComplex U) _ (sheafComplex_exact U)
          (augmentation U) (augmentation_zero U) (augmentation_exact U) n
          (vertexTwistPullCycles R f a b hb U' U hU n z)) := by
  let _ := augmentation_epi U' hc'
  let _ := augmentation_epi U hc
  have hcl := cellPull_class (vertexSchemeMap R f).base U U' hU hc hc'
    (vertexTwistAbelianSheaf R V a) n z
  rw [vertexTwistHPullback_apply, vertexModuleHPullback, moduleSheafHPullback_apply]
  erw [hcl]
  rw [← Sheaf.H.map_comp_apply]
  change Sheaf.H.map (vertexTwistPullComparison R f a b hb) n _ = _
  erw [← localSheafTopEquiv_naturality (vertexTwistPullComparison R f a b hb)]
  congr 1
  unfold augmentedComplexCocycleComparison
  rw [Ext.comp_assoc_of_third_deg_zero, ← ExactTower.cocycleComparison_postcomp]
  rfl

/-- Pulled back twist sections commute with restriction. -/
theorem vertexTwistPullSection_restrict {O O' : (vertexScheme R V).Opens} (h : O' ≤ O)
    (s : Γ(vertexTwistSheaf R V a, O)) :
    vertexTwistPullSection R f a b hb O' ((vertexTwistSheaf R V a).presheaf.map (homOfLE h).op s) =
      (vertexTwistSheaf R W b).presheaf.map (homOfLE ((vertexSchemeMap R f).preimage_mono h)).op
        (vertexTwistPullSection R f a b hb O s) := by
  unfold vertexTwistPullSection
  have h1 := ConcreteCategory.congr_hom
    ((((Scheme.Modules.pullbackPushforwardAdjunction (vertexSchemeMap R f)).unit.app
      (vertexTwistSheaf R V a))).mapPresheaf.naturality (homOfLE h).op) s
  have h2 := ConcreteCategory.congr_hom
    ((vertexTwistPullbackIso R f a b hb).hom.mapPresheaf.naturality
      (homOfLE ((vertexSchemeMap R f).preimage_mono h)).op)
    ((((Scheme.Modules.pullbackPushforwardAdjunction (vertexSchemeMap R f)).unit.app
      (vertexTwistSheaf R V a)).app O) s)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h1 h2
  erw [h1]
  exact h2

omit [DecidableEq V] in
/-- **Face sections of the pulled back cocycle**: the restricted pulled back twist sections
(`vertexTwistPullSection`) of the face sections of the cocycle. -/
theorem sectionsEquiv_vertexTwistPullCycles (n : ℕ)
    (z : (cubicalTower U').cycles (vertexTwistAbelianSheaf R V a) n) (q : FaceIndex (V := I) n) :
    sectionsEquiv U (vertexTwistAbelianSheaf R W b) n (vertexTwistPullCycles R f a b hb U' U hU n z).val q =
      (vertexTwistSheaf R W b).presheaf.map
        (homOfLE (faceOpen_pull (vertexSchemeMap R f).base U U' hU q.val).ge).op
        (vertexTwistPullSection R f a b hb _
          (sectionsEquiv U' (vertexTwistAbelianSheaf R V a) n z.val q)) := by
  rw [vertexTwistPullCycles_val, ← Category.assoc, sectionsEquiv_comp,
    sectionsEquiv_cellPullComponent_comp]
  rw [← ConcreteCategory.comp_apply, (vertexTwistPullComparison R f a b hb).hom.naturality,
    ConcreteCategory.comp_apply]
  congr 1
  change ((SheafOfModules.toSheaf (vertexScheme R W).ringCatSheaf).map
      (vertexTwistPullbackIso R f a b hb).hom).hom.app _
    ((moduleSheafPullbackComparison (vertexSchemeMap R f) (vertexTwistSheaf R V a)).hom.app _
      (topPullSection (vertexSchemeMap R f).base _ _ _)) = _
  rw [moduleSheafPullbackComparison_topPullSection]
  rfl

end Transport

section Injective

variable (R : Type) [CommRing R] {V W : Type} [Fintype V] [Fintype W] [DecidableEq V]
  [DecidableEq W] {j : V → W} (hj : Function.Injective j)

omit [DecidableEq V] [DecidableEq W] in
/-- The coordinate map of `j` pulls back the coordinate opens of `V` to the coordinate opens of the
images. -/
theorem vertexSchemeMap_map_coordinateOpen (f : V → W) (v : V) (c : Fin 2) :
    (Opens.map (vertexSchemeMap R f).base).obj (vertexCoordinateOpen R V v c) =
      vertexCoordinateOpen R W (f v) c :=
  vertexSchemeMap_preimage_coordinateOpen R f v c

/-- **Face coordinates of the relabelled pulled back cocycle** along an injective vertex map. -/
theorem vertexTwistPullCycles_relabel_faceSections (d : V → ℕ) (d' : W → ℕ)
    (hneg : ∀ w, -(d' w : ℤ) = ∑ v ∈ Finset.univ.filter (fun v => j v = w), -(d v : ℤ)) (n : ℕ)
    (z : (cubicalTower (vertexCoordinateOpen R V)).cycles
      (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n)
    (q : FaceIndex (V := W) n) :
    vertexTwistSheafFaceSectionsEquiv R W (fun w => -(d' w : ℤ)) q.val
        (sectionsEquiv (vertexCoordinateOpen R W) _ n
          ((relabelSheafComplex (vertexCoordinateOpen R W) (fun v => vertexCoordinateOpen R W (j v))
            hj (fun _ _ => le_rfl)).f n ≫
            (vertexTwistPullCycles R j (fun v => -(d v : ℤ)) (fun w => -(d' w : ℤ)) hneg
              (vertexCoordinateOpen R V) (fun v => vertexCoordinateOpen R W (j v))
              (vertexSchemeMap_map_coordinateOpen R j) n z).val) q) =
      if h : ∀ w, q.val w = 2 → ∃ v, j v = w then
        CechCubicalCell.relabelCoefficient ℤ j q.val • facePull j q.val R
          (vertexTwistSheafFaceSectionsEquiv R V (fun v => -(d v : ℤ)) (fun v => q.val (j v))
            (sectionsEquiv (vertexCoordinateOpen R V) _ n z.val (relabelFace hj q h)))
      else 0 := by
  rw [sectionsEquiv_relabel]
  by_cases h : ∀ w, q.val w = 2 → ∃ v, j v = w
  · rw [dite_eq_left h, dite_eq_left h, map_zsmul, sectionsEquiv_vertexTwistPullCycles]
    congr 1
    rw [← vertexTwistPullSection_faceSections R j _ _ hneg q.val]
    congr 1
    exact modulePresheaf_map_map _ _ _ _ _
  · rw [dite_eq_right h, dite_eq_right h, map_zero]

variable [IsNoetherianRing R]

include hj in
/-- **The multi-twist state formula for injective vertex maps.** For an injective `j : V → W`, a
nonnegative twist `d` on `V` and its extension `d'` by zero, the state coordinates of the pullback
of a class along `a_j` are the Koszul sign `vertexMapSign R j (twistSupport d)` times the state
coordinates at the restricted index `hPull hd κ`, in every degree. -/
theorem vertexTwistActualStateAt_pullback_of_injective (d : V → ℕ) (d' : W → ℕ)
    (hd : ∀ v, d' (j v) = d v) (hd0 : ∀ w, (∀ v, j v ≠ w) → d' w = 0)
    (hneg : ∀ w, -(d' w : ℤ) = ∑ v ∈ Finset.univ.filter (fun v => j v = w), -(d v : ℤ)) (n : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n) (κ : HBasis d') :
    (vertexTwistActualStateAt R W d' n
        (vertexTwistHPullback R j (fun v => -(d v : ℤ)) (fun w => -(d' w : ℤ)) hneg n x)).val κ =
      vertexMapSign R j (twistSupport d) * (vertexTwistActualStateAt R V d n x).val (hPull hd κ) := by
  let _ := augmentation_epi (vertexCoordinateOpen R V) (vertexCellChartOpen_cover R V)
  let _ := augmentation_epi (vertexCoordinateOpen R W) (vertexCellChartOpen_cover R W)
  let _ := augmentation_epi (fun v => vertexCoordinateOpen R W (j v))
    (vertexRelabelChartOpen_cover R W j)
  set s := vertexTwistActualStateAt R V d n x with hs
  set z := vertexTwistCellStateInclusion R V d n s with hz
  have hx : x = vertexTwistCellActualAtLinearEquiv R V (fun v => -(d v : ℤ)) n
      ((cubicalTower (vertexCoordinateOpen R V)).classAt _ n z) := by
    apply vertexTwistActualStateAt_injective R V d n
    rw [vertexTwistActualStateAt_actual, vertexTwistCellStateAt_class,
      vertexTwistCellCycleProjection_inclusion]
  set w := vertexTwistPullCycles R j (fun v => -(d v : ℤ)) (fun w => -(d' w : ℤ)) hneg
    (vertexCoordinateOpen R V) (fun v => vertexCoordinateOpen R W (j v))
    (vertexSchemeMap_map_coordinateOpen R j) n z with hw
  set y := (complexSourceMap (relabelSheafComplex (vertexCoordinateOpen R W)
    (fun v => vertexCoordinateOpen R W (j v)) hj (fun _ _ => le_rfl)) (sheafComplex_exact _)
      (sheafComplex_exact _)).cycles _ n w with hy
  have himage : vertexTwistHPullback R j (fun v => -(d v : ℤ)) (fun w => -(d' w : ℤ)) hneg n x =
      vertexTwistCellActualAtLinearEquiv R W (fun w => -(d' w : ℤ)) n
        ((cubicalTower (vertexCoordinateOpen R W)).classAt _ n y) := by
    rw [hx]
    change vertexTwistHPullback R j (fun v => -(d v : ℤ)) (fun w => -(d' w : ℤ)) hneg n
        (finiteCubicalActualAtEquiv (vertexCoordinateOpen R V) _ (vertexCellChartOpen_cover R V)
          (vertexTwistCellSheaf_terms_acyclic R V _) n
            ((cubicalTower (vertexCoordinateOpen R V)).classAt _ n z)) =
      finiteCubicalActualAtEquiv (vertexCoordinateOpen R W) _ (vertexCellChartOpen_cover R W)
        (vertexTwistCellSheaf_terms_acyclic R W _) n
          ((cubicalTower (vertexCoordinateOpen R W)).classAt _ n y)
    rw [finiteCubicalActualAtEquiv_class, finiteCubicalActualAtEquiv_class]
    erw [vertexTwistHPullback_cellClass R j _ _ hneg (vertexCoordinateOpen R V)
      (fun v => vertexCoordinateOpen R W (j v)) (vertexSchemeMap_map_coordinateOpen R j)
      (vertexCellChartOpen_cover R V) (vertexRelabelChartOpen_cover R W j) n z]
    congr 1
    exact (relabel_cocycleComparison (vertexCoordinateOpen R W)
      (fun v => vertexCoordinateOpen R W (j v)) hj (fun _ _ => le_rfl)
      (vertexCellChartOpen_cover R W) (vertexRelabelChartOpen_cover R W j) _ n w).symm
  rw [himage, vertexTwistActualStateAt_actual, vertexTwistCellStateAt_class,
    vertexTwistCellCycleProjection_val,
    vertexTwistCellCoefficientEquiv_eq_cechExtend R hj d d' n z.val y.val
      (vertexTwistPullCycles_relabel_faceSections R hj d d' hneg n z),
    vertexTwistCellStateInclusion_coefficient]
  exact contraction_p_cechExtend_i R hj d d' hd hd0 s.val κ

end Injective

section Support

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- The twist support of `d` as a vertex type. -/
abbrev TwistSupportType (d : V → ℕ) := {v // v ∈ twistSupport d}

/-- The twist `d` restricted to its support. -/
def supportTwist (d : V → ℕ) : TwistSupportType d → ℕ := fun a => d a.1

/-- Extension of a state index of the restricted twist by the `H⁰` index off the support. -/
noncomputable def supportExtendIdx (d : V → ℕ) (κ : HBasis (supportTwist d)) : HBasis d :=
  fun v => if hv : v ∈ twistSupport d then κ ⟨v, hv⟩ else
    ⟨0, by rw [mem_twistSupport, not_not] at hv; rw [hv, phi_zero]; exact Nat.one_pos⟩

/-- The values of an extended state index. -/
theorem supportExtendIdx_val (d : V → ℕ) (κ : HBasis (supportTwist d)) (v : V) :
    (supportExtendIdx d κ v).val = if hv : v ∈ twistSupport d then (κ ⟨v, hv⟩).val else 0 := by
  unfold supportExtendIdx
  split_ifs <;> rfl

/-- Two state indices with the same values are equal. -/
theorem hBasis_ext {d : V → ℕ} {κ κ' : HBasis d} (h : ∀ v, (κ v).val = (κ' v).val) : κ = κ' :=
  funext fun v => Fin.ext (h v)

/-- The twist vanishes off its support. -/
theorem eq_zero_of_not_mem_twistSupport {d : V → ℕ} {v : V} (hv : v ∉ twistSupport d) : d v = 0 := by
  rw [mem_twistSupport, not_not] at hv
  exact hv

/-- Extending a restricted state index recovers the state index. -/
theorem supportExtendIdx_hPull (d : V → ℕ) (κ : HBasis d) :
    supportExtendIdx d (hPull (j := fun a : TwistSupportType d => a.1)
      (d := supportTwist d) (d' := d) (fun _ => rfl) κ) = κ := by
  apply hBasis_ext
  intro v
  rw [supportExtendIdx_val]
  split_ifs with hv
  · rfl
  · have h1 : phi (d v) = 1 := by rw [eq_zero_of_not_mem_twistSupport hv, phi_zero]
    have hlt := (κ v).isLt
    omega

/-- The restricted twist has full support. -/
theorem twistSupport_supportTwist (d : V → ℕ) : twistSupport (supportTwist d) = Finset.univ := by
  ext a
  simp only [mem_twistSupport, Finset.mem_univ, iff_true]
  exact (mem_twistSupport (d := d)).1 a.2

/-- The cohomological degree of the restricted twist is that of the twist. -/
theorem cohomologyDegree_supportTwist (d : V → ℕ) :
    cohomologyDegree (supportTwist d) = cohomologyDegree d := by
  rw [cohomologyDegree_eq_card_twistSupport, cohomologyDegree_eq_card_twistSupport,
    twistSupport_supportTwist, Finset.card_univ, Fintype.card_coe]

variable (f : V → W) {d : V → ℕ} {d' : W → ℕ}
  (hneg : ∀ w, -(d' w : ℤ) = ∑ v ∈ Finset.univ.filter (fun v => f v = w), -(d v : ℤ))

include hneg in
/-- The pushed forward twist is the fibrewise sum. -/
theorem pushTwist_eq_sum (w : W) : d' w = ∑ v ∈ Finset.univ.filter (fun v => f v = w), d v := by
  have h := hneg w
  rw [Finset.sum_neg_distrib, neg_inj] at h
  exact_mod_cast h

variable (hd : ∀ v, d v ≠ 0 → d' (f v) = d v)

include hneg hd in
/-- A vertex function whose pushed forward twist agrees with the twist on its support is
injective on the support. -/
theorem injOn_twistSupport : Set.InjOn f (twistSupport d : Set V) := by
  intro v₁ h₁ v₂ h₂ he
  by_contra hne
  have h₁' : d v₁ ≠ 0 := mem_twistSupport.1 h₁
  have h₂' : d v₂ ≠ 0 := mem_twistSupport.1 h₂
  have hs := pushTwist_eq_sum f hneg (f v₁)
  rw [hd v₁ h₁'] at hs
  have hm₁ : v₁ ∈ Finset.univ.filter (fun v => f v = f v₁) := by simp
  have hm₂ : v₂ ∈ (Finset.univ.filter (fun v => f v = f v₁)).erase v₁ := by
    simp [Ne.symm hne, he.symm]
  rw [← Finset.add_sum_erase _ _ hm₁] at hs
  have hle := Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) hm₂
  omega

include hneg hd in
/-- The composite of `f` with the inclusion of the twist support is injective. -/
theorem injective_comp_support : Function.Injective (fun a : TwistSupportType d => f a.1) := by
  intro a₁ a₂ he
  exact Subtype.ext (injOn_twistSupport f hneg hd a₁.2 a₂.2 he)

include hneg in
/-- The pushed forward twist vanishes off the image of the support. -/
theorem pushTwist_eq_zero (w : W) (hw : ∀ a : TwistSupportType d, f a.1 ≠ w) : d' w = 0 := by
  rw [pushTwist_eq_sum f hneg w]
  refine Finset.sum_eq_zero fun v hv => ?_
  by_contra hne
  exact hw ⟨v, mem_twistSupport.2 hne⟩ (Finset.mem_filter.1 hv).2

include hd in
/-- On the support, the pushed forward twist is the twist. -/
theorem pushTwist_support (a : TwistSupportType d) : d' (f a.1) = supportTwist d a :=
  hd a.1 (mem_twistSupport.1 a.2)

include hd in
/-- Extending the restriction of a state index of `d'` is the pulled back state index. -/
theorem supportExtendIdx_hPull_comp (κ : HBasis d') :
    supportExtendIdx d (hPull (j := fun a : TwistSupportType d => f a.1) (d := supportTwist d)
      (d' := d') (pushTwist_support f hd) κ) = hPullTwist f hd κ := by
  apply hBasis_ext
  intro v
  rw [supportExtendIdx_val, hPullTwist_val]
  split_ifs with h1 h2 h2
  · exact absurd h2 (mem_twistSupport.1 h1)
  · rfl
  · rfl
  · exact absurd (mem_twistSupport.2 h2) h1

end Support

section General

variable (R : Type) [CommRing R] {V W : Type} [Fintype V] [Fintype W] [DecidableEq V]
  [DecidableEq W]

/-- The state vector restricted to the twist support, signed so that its pullback along the
inclusion of the support is the original state vector. -/
noncomputable def supportStates (d : V → ℕ) (n : ℕ) (s : stateDegreePiece R d n) :
    stateDegreePiece R (supportTwist d) n :=
  ⟨Finsupp.equivFunOnFinite.symm fun κ =>
      vertexMapSign R (fun a : TwistSupportType d => a.1) (twistSupport (supportTwist d)) *
        s.val (supportExtendIdx d κ), by
    rw [Finsupp.mem_supported]
    intro κ hκ
    change (cohomologyDegree (supportTwist d) : ℤ) = n
    rw [cohomologyDegree_supportTwist]
    have hne : s.val (supportExtendIdx d κ) ≠ 0 := by
      intro h0
      apply Finsupp.mem_support_iff.1 hκ
      simp [h0]
    exact (Finsupp.mem_supported _ _).1 s.property (Finsupp.mem_support_iff.2 hne)⟩

/-- The values of the restricted state vector. -/
theorem supportStates_apply (d : V → ℕ) (n : ℕ) (s : stateDegreePiece R d n)
    (κ : HBasis (supportTwist d)) :
    (supportStates R d n s).val κ =
      vertexMapSign R (fun a : TwistSupportType d => a.1) (twistSupport (supportTwist d)) *
        s.val (supportExtendIdx d κ) := by
  simp [supportStates]

variable [IsNoetherianRing R]

/-- **The multi-twist state formula for vertex functions.** For every function `f : V → W` (vertices
may be identified and missed), every nonnegative twist `d` on `V` whose support is not collided by
`f`, and its pushforward `d'`, the state coordinates of the pullback along `a_f` are the Koszul sign
of the support times the state coordinates at the pulled-back index, in every degree. -/
theorem vertexMapTwistStateFormula (f : V → W) : VertexMapTwistStateFormula R f := by
  intro d d' hneg hd n x κ
  -- the inclusion of the twist support
  let ι : TwistSupportType d → V := fun a => a.1
  have hι : Function.Injective ι := Subtype.val_injective
  have hdA : ∀ a : TwistSupportType d, d (ι a) = supportTwist d a := fun _ => rfl
  have hdA0 : ∀ v, (∀ a : TwistSupportType d, ι a ≠ v) → d v = 0 := by
    intro v hv
    by_contra hne
    exact hv ⟨v, mem_twistSupport.2 hne⟩ rfl
  have hnegA : ∀ v, -(d v : ℤ) =
      ∑ a ∈ Finset.univ.filter (fun a : TwistSupportType d => ι a = v),
        -(supportTwist d a : ℤ) := by
    intro v
    by_cases hv : v ∈ twistSupport d
    · rw [Finset.sum_eq_single ⟨v, hv⟩]
      · rfl
      · intro a ha hne
        exact absurd (Subtype.ext (Finset.mem_filter.1 ha).2) hne
      · intro h
        exact absurd (by simp [ι]) h
    · rw [eq_zero_of_not_mem_twistSupport hv, Finset.sum_eq_zero]
      · simp
      · intro a ha
        exact absurd ((Finset.mem_filter.1 ha).2 ▸ a.2) hv
  -- the restricted class
  set s := vertexTwistActualStateAt R V d n x with hs
  set zA := vertexTwistCellStateInclusion R (TwistSupportType d) (supportTwist d) n
    (supportStates R d n s) with hzA
  set xA := vertexTwistCellActualAtLinearEquiv R (TwistSupportType d)
    (fun a => -(supportTwist d a : ℤ)) n
    ((cubicalTower (vertexCoordinateOpen R (TwistSupportType d))).classAt _ n zA) with hxA
  have hsA : vertexTwistActualStateAt R (TwistSupportType d) (supportTwist d) n xA =
      supportStates R d n s := by
    rw [hxA, vertexTwistActualStateAt_actual, vertexTwistCellStateAt_class,
      vertexTwistCellCycleProjection_inclusion]
  have hx : x = vertexTwistHPullback R ι (fun a => -(supportTwist d a : ℤ))
      (fun v => -(d v : ℤ)) hnegA n xA := by
    apply vertexTwistActualStateAt_injective R V d n
    apply Subtype.ext
    ext κ'
    rw [vertexTwistActualStateAt_pullback_of_injective R hι (supportTwist d) d hdA hdA0 hnegA n xA κ',
      hsA, supportStates_apply, supportExtendIdx_hPull, ← mul_assoc, vertexMapSign_mul_self, one_mul]
  -- the cover of `(P¹)^V` indexed by the support, and its preimage cover of `(P¹)^W`
  let j : TwistSupportType d → W := fun a => f a.1
  have hj : Function.Injective j := injective_comp_support f hneg hd
  have hdj : ∀ a, d' (j a) = supportTwist d a := pushTwist_support f hd
  have hdj0 : ∀ w, (∀ a, j a ≠ w) → d' w = 0 := pushTwist_eq_zero f hneg
  let _ := augmentation_epi (vertexCoordinateOpen R (TwistSupportType d))
    (vertexCellChartOpen_cover R (TwistSupportType d))
  let _ := augmentation_epi (fun a => vertexCoordinateOpen R V (ι a))
    (vertexRelabelChartOpen_cover R V ι)
  let _ := augmentation_epi (fun a => vertexCoordinateOpen R W (j a))
    (vertexRelabelChartOpen_cover R W j)
  let _ := augmentation_epi (vertexCoordinateOpen R W) (vertexCellChartOpen_cover R W)
  set c := vertexTwistPullCycles R ι (fun a => -(supportTwist d a : ℤ)) (fun v => -(d v : ℤ)) hnegA
    (vertexCoordinateOpen R (TwistSupportType d)) (fun a => vertexCoordinateOpen R V (ι a))
    (vertexSchemeMap_map_coordinateOpen R ι) n zA with hc
  set c' := vertexTwistPullCycles R f (fun v => -(d v : ℤ)) (fun w => -(d' w : ℤ)) hneg
    (fun a => vertexCoordinateOpen R V (ι a)) (fun a => vertexCoordinateOpen R W (j a))
    (fun a e => vertexSchemeMap_map_coordinateOpen R f (ι a) e) n c with hc'
  set y := (complexSourceMap (relabelSheafComplex (vertexCoordinateOpen R W)
    (fun a => vertexCoordinateOpen R W (j a)) hj (fun _ _ => le_rfl)) (sheafComplex_exact _)
      (sheafComplex_exact _)).cycles _ n c' with hy
  have himage : vertexTwistHPullback R f (fun v => -(d v : ℤ)) (fun w => -(d' w : ℤ)) hneg n x =
      vertexTwistCellActualAtLinearEquiv R W (fun w => -(d' w : ℤ)) n
        ((cubicalTower (vertexCoordinateOpen R W)).classAt _ n y) := by
    rw [hx]
    change vertexTwistHPullback R f (fun v => -(d v : ℤ)) (fun w => -(d' w : ℤ)) hneg n
        (vertexTwistHPullback R ι (fun a => -(supportTwist d a : ℤ)) (fun v => -(d v : ℤ)) hnegA n
          (finiteCubicalActualAtEquiv (vertexCoordinateOpen R (TwistSupportType d)) _
            (vertexCellChartOpen_cover R _) (vertexTwistCellSheaf_terms_acyclic R _ _) n
              ((cubicalTower (vertexCoordinateOpen R (TwistSupportType d))).classAt _ n zA))) =
      finiteCubicalActualAtEquiv (vertexCoordinateOpen R W) _ (vertexCellChartOpen_cover R W)
        (vertexTwistCellSheaf_terms_acyclic R W _) n
          ((cubicalTower (vertexCoordinateOpen R W)).classAt _ n y)
    rw [finiteCubicalActualAtEquiv_class, finiteCubicalActualAtEquiv_class]
    erw [vertexTwistHPullback_cellClass R ι _ _ hnegA (vertexCoordinateOpen R (TwistSupportType d))
      (fun a => vertexCoordinateOpen R V (ι a)) (vertexSchemeMap_map_coordinateOpen R ι)
      (vertexCellChartOpen_cover R _) (vertexRelabelChartOpen_cover R V ι) n zA]
    erw [vertexTwistHPullback_cellClass R f _ _ hneg (fun a => vertexCoordinateOpen R V (ι a))
      (fun a => vertexCoordinateOpen R W (j a)) (fun a e => vertexSchemeMap_map_coordinateOpen R f (ι a) e)
      (vertexRelabelChartOpen_cover R V ι) (vertexRelabelChartOpen_cover R W j) n c]
    congr 1
    exact (relabel_cocycleComparison (vertexCoordinateOpen R W)
      (fun a => vertexCoordinateOpen R W (j a)) hj (fun _ _ => le_rfl)
      (vertexCellChartOpen_cover R W) (vertexRelabelChartOpen_cover R W j) _ n c').symm
  have hfaces : ∀ q : FaceIndex (V := W) n,
      vertexTwistSheafFaceSectionsEquiv R W (fun w => -(d' w : ℤ)) q.val
          (sectionsEquiv (vertexCoordinateOpen R W) _ n y.val q) =
        if h : ∀ w, q.val w = 2 → ∃ a, j a = w then
          CechCubicalCell.relabelCoefficient ℤ j q.val • facePull j q.val R
            (vertexTwistSheafFaceSectionsEquiv R (TwistSupportType d)
              (fun a => -(supportTwist d a : ℤ)) (fun a => q.val (j a))
              (sectionsEquiv (vertexCoordinateOpen R (TwistSupportType d)) _ n zA.val
                (relabelFace hj q h)))
        else 0 := by
    intro q
    rw [show y.val = (relabelSheafComplex (vertexCoordinateOpen R W)
      (fun a => vertexCoordinateOpen R W (j a)) hj (fun _ _ => le_rfl)).f n ≫ c'.val from rfl,
      sectionsEquiv_relabel]
    by_cases h : ∀ w, q.val w = 2 → ∃ a, j a = w
    · rw [dite_eq_left h, dite_eq_left h, map_zsmul]
      congr 1
      rw [hc', sectionsEquiv_vertexTwistPullCycles, hc, sectionsEquiv_vertexTwistPullCycles]
      set t := sectionsEquiv (vertexCoordinateOpen R (TwistSupportType d)) _ n zA.val
        (relabelFace hj q h)
      have hY : binaryCoverFaceOpen (vertexCoordinateOpen R V) (fun v => q.val (f v)) ≤
          binaryCoverFaceOpen (fun a => vertexCoordinateOpen R V (ι a)) (fun a => q.val (j a)) :=
        le_iInf fun a => iInf_le
          (fun v => binaryCoverFaceFactor (vertexCoordinateOpen R V v) (q.val (f v))) (ι a)
      set X := (vertexTwistSheaf R V (fun v => -(d v : ℤ))).presheaf.map
        (homOfLE (faceOpen_pull (vertexSchemeMap R ι).base (fun a => vertexCoordinateOpen R V (ι a))
          (vertexCoordinateOpen R (TwistSupportType d)) (vertexSchemeMap_map_coordinateOpen R ι)
          (relabelFace hj q h).val).ge).op
        (vertexTwistPullSection R ι (fun a => -(supportTwist d a : ℤ)) (fun v => -(d v : ℤ)) hnegA _ t)
        with hX
      have e1 : (vertexTwistSheaf R W (fun w => -(d' w : ℤ))).presheaf.map
          (homOfLE (binaryCoverFaceOpen_relabel_le (vertexCoordinateOpen R W)
            (fun a => vertexCoordinateOpen R W (j a)) (fun _ _ => le_rfl) q.val)).op
          ((vertexTwistSheaf R W (fun w => -(d' w : ℤ))).presheaf.map
            (homOfLE (faceOpen_pull (vertexSchemeMap R f).base (fun a => vertexCoordinateOpen R W (j a))
              (fun a => vertexCoordinateOpen R V (ι a))
              (fun a e => vertexSchemeMap_map_coordinateOpen R f (ι a) e)
              (relabelFace hj q h).val).ge).op
            (vertexTwistPullSection R f (fun v => -(d v : ℤ)) (fun w => -(d' w : ℤ)) hneg _ X)) =
          (vertexTwistSheaf R W (fun w => -(d' w : ℤ))).presheaf.map
            (homOfLE (vertexFaceOpen_le_preimage R f q.val)).op
            (vertexTwistPullSection R f (fun v => -(d v : ℤ)) (fun w => -(d' w : ℤ)) hneg _
              ((vertexTwistSheaf R V (fun v => -(d v : ℤ))).presheaf.map (homOfLE hY).op X)) := by
        rw [vertexTwistPullSection_restrict R f _ _ hneg hY X]
        exact modulePresheaf_map_map_eq _ _ _ _ _ _
      have e2 : (vertexTwistSheaf R V (fun v => -(d v : ℤ))).presheaf.map (homOfLE hY).op X =
          (vertexTwistSheaf R V (fun v => -(d v : ℤ))).presheaf.map
            (homOfLE (vertexFaceOpen_le_preimage R ι (fun v => q.val (f v)))).op
            (vertexTwistPullSection R ι (fun a => -(supportTwist d a : ℤ)) (fun v => -(d v : ℤ))
              hnegA _ t) :=
        modulePresheaf_map_map _ _ _ _ _
      erw [e1, vertexTwistPullSection_faceSections R f _ _ hneg q.val, e2,
        vertexTwistPullSection_faceSections R ι _ _ hnegA (fun v => q.val (f v))]
      exact facePull_comp ι f q.val R _
    · rw [dite_eq_right h, dite_eq_right h, map_zero]
  rw [himage, vertexTwistActualStateAt_actual, vertexTwistCellStateAt_class,
    vertexTwistCellCycleProjection_val,
    vertexTwistCellCoefficientEquiv_eq_cechExtend R hj (supportTwist d) d' n zA.val y.val hfaces,
    vertexTwistCellStateInclusion_coefficient,
    contraction_p_cechExtend_i R hj (supportTwist d) d' hdj hdj0 _ κ, supportStates_apply,
    supportExtendIdx_hPull_comp f hd κ, ← mul_assoc]
  congr 1
  have himg : Finset.univ.image ι = twistSupport d := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro hv
      exact ⟨⟨v, hv⟩, rfl⟩
  have hg : Set.InjOn f ↑(Finset.univ.image ι) := by
    rw [himg]
    exact injOn_twistSupport f hneg hd
  have hcomp := vertexMapSign_comp R ι f Finset.univ hι.injOn hg
  rw [himg] at hcomp
  rw [twistSupport_supportTwist]
  change vertexMapSign R (f ∘ ι) Finset.univ * vertexMapSign R ι Finset.univ = _
  rw [hcomp, mul_assoc, vertexMapSign_mul_self, mul_one]

end General

/-! ## Exterior consequences -/

namespace VertexMap

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexMap G H)

/-- **Exterior state formula for vertex maps.** At a state `b` of `H` whose edge set has injective
vertex support in `G`, the state coordinate of the geometric image of an exterior class is the
Koszul sign `vertexMapSign R φ.vertex (G.support b.1)` times the coordinate of the class at the
restricted state `φ.statePullOn b h`, exactly as on the Tor side. -/
theorem exteriorCohomologyState_pullback (R : Type) [CommRing R] [IsNoetherianRing R] (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) (b : H.IncResolutionBasis)
    (h : Set.InjOn φ.vertex (G.support b.1)) :
    H.exteriorCohomologyState R q j (φ.exteriorCohomologyPullback R q j x) b =
      vertexMapSign R φ.vertex (G.support b.1) *
        G.exteriorCohomologyState R q j x (φ.statePullOn b h) :=
  φ.exteriorCohomologyState_pullback_of R (vertexMapTwistStateFormula R φ.vertex) q j x b h

/-- **The naturality square for vertex maps.** The Tor-to-exterior isomorphism carries the Tor map
of a vertex map (Mathlib's derived functor functoriality) to the geometric map of exterior
cohomology induced by the coordinate map `a_φ`, for vertex maps that may identify vertices. -/
theorem incidenceTorExteriorEquiv_vertexMap {p q : ℕ} (h : p ≤ q)
    (y : G.incidenceTorInternalPiece p q) :
    H.incidenceTorExteriorEquiv h (φ.incidenceTorInternalVertexMap p q y) =
      φ.exteriorCohomologyPullback ℂ q (q - p) (G.incidenceTorExteriorEquiv h y) :=
  φ.incidenceTorExteriorEquiv_vertexMap_of (vertexMapTwistStateFormula ℂ φ.vertex) h y

end VertexMap

end BPFixedPoints.Multigraph
