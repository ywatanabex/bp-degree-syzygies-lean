import BPFixedPoints.Incidence.IncidenceKernelSheafSections
import BPFixedPoints.Incidence.IncidenceKernelBundleEdgeSheaf
import BPFixedPoints.Incidence.SchemeModuleHomGluing
import BPFixedPoints.Incidence.EdgeExteriorChart
import BPFixedPoints.Incidence.VertexProjectiveTwistTensorFrames
import BPFixedPoints.Incidence.SchemeModuleGeometricCoefficients

/-! # The evaluation `O^{4m} → F_G` as a morphism of sheaves of modules

This file starts the sheaf-level part of the paper's Lemma `alg:incidence-vector-bundle`
(supplement section `supp:vector-bundle`). On `X_G = vertexScheme ℂ V = (ℙ¹)^V`, the trivial
bundle `O^{4m} = incCoeffSheaf V E` is the finite biproduct of copies of the structure sheaf
indexed by the coefficients `c_{e,α,β}`, and `F_G = G.edgeBundle ℂ` is the finite biproduct of
the edge line sheaves `L_e = edgeLineSheaf ℂ e` (`EdgeExteriorBundle.lean`).

* **Charts and faces.** The chart opens `incChartOpen V σ` (`σ : V → Bool`) cover `X_G`
  (`incChartOpen_iSup_top`), and the overlap of two charts lies in the face open of the join of
  their chart faces (`incChartOpen_inf_le_faceJoin`): this identifies the chart overlaps with
  face opens, where the face coordinates `vertexFaceSectionsEquiv` apply. The chart coordinates
  `t_v` are functions on the chart open (`incChartCoordinate`), and on the face open of a face
  `r` refined by `σ` they are the restricted chart point `incOverlapPoint hσ`
  (`vertexFaceSectionsEquiv_incChartPoint`).
* **Local entries.** On chart `σ`, the entry of the coefficient `c_{e,α,β}` is the morphism
  `O → L_e` of sheaves of modules on the over-site of the chart given by multiplication by the
  chart monomial `X_{fst e,α}(t) X_{snd e,β}(t)` followed by the inverse chart frame of `L_e`
  (`incEntryLocal`, `incEntryLocal_coefficient`). In the frame of any face `r` refined by `σ`
  it is multiplication by the face monomial, independently of `σ`
  (`incEntryLocal_faceCoefficient`); this uses the edge units as transition coefficients of
  `edgeLineSheaf` (`edgeLineSheaf_pairTransition`) and the overlap formula
  `incChartMonomial_overlapPoint`. Hence the local entries agree on chart overlaps
  (`incEntryLocal_compatible`).
* **Gluing.** `moduleHomGlue` glues them to global morphisms `O → L_e` (`incEntrySheafMap`,
  restricting to the local entries by `incEntrySheafMap_over`), and the evaluation map
  `incEvaluationSheafMap : O^{4m} ⟶ F_G` is the morphism of sheaves of modules whose `L_e`
  component is `Σ_{α,β} c_{e,α,β} s_{e,α,β}`.
* **Chart form.** On every subopen `W` of chart `σ`, in the coefficient frame of `O^{4m}`
  (`incCoeffSectionsEquiv`) and the chart frame of `F_G` (`incEdgeChartEquiv`), the evaluation
  map is the chart evaluation map `incChartEvaluation σ` of `IncidenceVectorBundleCharts.lean` at
  the chart point of `W` (`incEvaluationSheafMap_chart`).

The kernel of the evaluation map and its local freeness are in
`IncidenceKernelSheafCharts.lean`. The surjectivity of the evaluation map as a morphism of
sheaves is not proved here.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CechProduct ProjectiveLine SheafTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

/-! ### Chart opens, face opens and chart coordinates -/

section Opens

variable (V) in
/-- The open of the standard chart `σ` of `X_G = (ℙ¹)^V`. -/
noncomputable abbrev incChartOpen (σ : V → Bool) : (vertexScheme ℂ V).Opens :=
  vertexChartOpen ℂ V (vertexBooleanPivot V σ)

variable (V) in
/-- The open of a Čech face `q` of `X_G`: the rectangular intersection of coordinate opens. -/
noncomputable abbrev incFaceOpen (q : V → Fin 3) : (vertexScheme ℂ V).Opens :=
  SheafTools.binaryCoverFaceOpen (vertexCoordinateOpen ℂ V) q

variable (V) in
/-- The standard charts `σ : V → Bool` cover `X_G`. -/
theorem incChartOpen_iSup_top : (⊤ : (vertexScheme ℂ V).Opens) ≤ ⨆ σ, incChartOpen V σ := by
  intro x hx
  obtain ⟨τ, hτ⟩ := TopologicalSpace.Opens.mem_iSup.mp (vertexChartOpen_iSup_top ℂ V hx)
  have h : vertexBooleanPivot V (fun v => decide (τ v = 1)) = τ := by
    have hb : ∀ i : Fin 2, (if decide (i = 1) = true then (1 : Fin 2) else 0) = i := by decide
    funext v
    exact hb (τ v)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨fun v => decide (τ v = 1), by rw [incChartOpen, h]; exact hτ⟩

/-- The overlap of two charts lies in the face open of the join of their chart faces. -/
theorem incChartOpen_inf_le_faceJoin (σ τ : V → Bool) :
    incChartOpen V σ ⊓ incChartOpen V τ ≤ incFaceOpen V (faceJoin (chartFace σ) (chartFace τ)) := by
  refine le_iInf fun v => ?_
  have hσ : incChartOpen V σ ≤ vertexCoordinateOpen ℂ V v (vertexBooleanPivot V σ v) := by
    rw [incChartOpen, vertexChartOpen_eq_coordinateOpen]
    exact iInf_le _ v
  have hτ : incChartOpen V τ ≤ vertexCoordinateOpen ℂ V v (vertexBooleanPivot V τ v) := by
    rw [incChartOpen, vertexChartOpen_eq_coordinateOpen]
    exact iInf_le _ v
  cases hs : σ v <;> cases ht : τ v
  · have h0 : vertexBooleanPivot V σ v = 0 := by simp [vertexBooleanPivot, hs]
    have hj : faceJoin (chartFace σ) (chartFace τ) v = 0 := by simp [faceJoin, chartFace, hs, ht]
    rw [h0] at hσ
    rw [hj]
    exact inf_le_left.trans hσ
  · have h0 : vertexBooleanPivot V σ v = 0 := by simp [vertexBooleanPivot, hs]
    have h1 : vertexBooleanPivot V τ v = 1 := by simp [vertexBooleanPivot, ht]
    have hj : faceJoin (chartFace σ) (chartFace τ) v = 2 := by simp [faceJoin, chartFace, hs, ht]
    rw [h0] at hσ
    rw [h1] at hτ
    rw [hj]
    exact le_inf (inf_le_left.trans hσ) (inf_le_right.trans hτ)
  · have h1 : vertexBooleanPivot V σ v = 1 := by simp [vertexBooleanPivot, hs]
    have h0 : vertexBooleanPivot V τ v = 0 := by simp [vertexBooleanPivot, ht]
    have hj : faceJoin (chartFace σ) (chartFace τ) v = 2 := by simp [faceJoin, chartFace, hs, ht]
    rw [h1] at hσ
    rw [h0] at hτ
    rw [hj]
    exact le_inf (inf_le_right.trans hτ) (inf_le_left.trans hσ)
  · have h1 : vertexBooleanPivot V σ v = 1 := by simp [vertexBooleanPivot, hs]
    have hj : faceJoin (chartFace σ) (chartFace τ) v = 1 := by simp [faceJoin, chartFace, hs, ht]
    rw [h1] at hσ
    rw [hj]
    exact inf_le_left.trans hσ

/-- Each chart open lies in the face open of its chart face. -/
theorem incChartOpen_le_chartFace (σ : V → Bool) :
    incChartOpen V σ ≤ incFaceOpen V (chartFace σ) := by
  have h := incChartOpen_inf_le_faceJoin σ σ
  have hj : faceJoin (chartFace σ) (chartFace σ) = chartFace σ := by
    funext v
    simp [faceJoin]
  rw [inf_idem, hj] at h
  exact h

/-- A face refined by chart `σ` lies in the chart open of `σ`. -/
theorem incFaceOpen_le_chart {σ : V → Bool} {r : V → Fin 3} (hσ : FaceRefines (chartFace σ) r) :
    incFaceOpen V r ≤ incChartOpen V σ :=
  vertexBinaryFaceOpen_le_chart ℂ V σ r hσ

/-- A face lies in the chart open of its own chart `vertexFaceBaseChoice V r`. -/
theorem incFaceOpen_le_baseChart (r : V → Fin 3) :
    incFaceOpen V r ≤ incChartOpen V (vertexFaceBaseChoice V r) :=
  incFaceOpen_le_chart (vertexFaceBaseChoice_refines V r)

end Opens

/-- Restriction of functions along two inclusions of opens is restriction along the composite. -/
theorem incPresheaf_restrict_restrict {W U U' : (vertexScheme ℂ V).Opens} (i : W ⟶ U) (j : U ⟶ U')
    (k : W ⟶ U') (x : Γ(vertexScheme ℂ V, U')) :
    (vertexScheme ℂ V).presheaf.map i.op ((vertexScheme ℂ V).presheaf.map j.op x) =
      (vertexScheme ℂ V).presheaf.map k.op x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

section Coordinates

/-- The affine coordinate `t_v` of the standard chart `σ`, as a function on the chart open: the
face variable of the chart face `chartFace σ`. -/
noncomputable def incChartCoordinate (σ : V → Bool) (v : V) :
    Γ(vertexScheme ℂ V, incChartOpen V σ) :=
  (vertexScheme ℂ V).presheaf.map (homOfLE (incChartOpen_le_chartFace σ)).op
    ((vertexFaceSectionsEquiv ℂ V (chartFace σ)).symm (faceVariable ℂ (chartFace σ) v))

/-- The point of chart `σ` over a subopen `W` of the chart: the restricted chart coordinates. -/
noncomputable def incChartPoint (σ : V → Bool) (W : (vertexScheme ℂ V).Opens)
    (hW : W ≤ incChartOpen V σ) : V → Γ(vertexScheme ℂ V, W) :=
  fun v => (vertexScheme ℂ V).presheaf.map (homOfLE hW).op (incChartCoordinate σ v)

/-- Chart points restrict to chart points. -/
theorem incChartPoint_restrict (σ : V → Bool) {W W' : (vertexScheme ℂ V).Opens} (h : W' ≤ W)
    (hW : W ≤ incChartOpen V σ) (v : V) :
    (vertexScheme ℂ V).presheaf.map (homOfLE h).op (incChartPoint σ W hW v) =
      incChartPoint σ W' (h.trans hW) v :=
  incPresheaf_restrict_restrict _ _ _ _

/-- **Chart coordinates on a face.** On the face open of a face `r` refined by chart `σ`, the
chart point of `σ` in face coordinates is the restricted chart point `incOverlapPoint hσ` of
`IncidenceKernelBundleTransitions.lean`. -/
theorem vertexFaceSectionsEquiv_incChartPoint {σ : V → Bool} {r : V → Fin 3}
    (hσ : FaceRefines (chartFace σ) r) (v : V) :
    vertexFaceSectionsEquiv ℂ V r (incChartPoint σ (incFaceOpen V r) (incFaceOpen_le_chart hσ) v) =
      incOverlapPoint hσ v := by
  rw [incChartPoint, incChartCoordinate,
    incPresheaf_restrict_restrict _ _ (homOfLE (vertexBinaryFaceOpen_refinement ℂ V hσ)),
    vertexFaceSections_restrict ℂ V hσ, RingEquiv.apply_symm_apply]
  rfl

end Coordinates

/-- The chart evaluation map commutes with ring homomorphisms. -/
theorem map_incChartEvaluation {R S F : Type*} [CommRing R] [CommRing S] [FunLike F R S]
    [RingHomClass F R S] (φ : F) (σ : V → Bool) (t : V → R) (c : IncCoeffIdx E → R) (e : E) :
    φ (G.incChartEvaluation σ t c e) =
      G.incChartEvaluation σ (fun v => φ (t v)) (fun c' => φ (c c')) e := by
  simp only [incChartEvaluation_apply, map_sum, map_mul, map_incChartMonomial]

/-! ### The local entries of the evaluation map -/

section Entries

/-- The chart monomial of the coefficient `c_{e,α,β}` on chart `σ`, as a function on the chart
open. -/
noncomputable def incChartMonomialFunction (σ : V → Bool) (e : E) (ab : Fin 2 × Fin 2) :
    Γ(vertexScheme ℂ V, incChartOpen V σ) :=
  G.incChartMonomial σ (incChartCoordinate σ) e ab

/-- The chart monomial function restricted to a subopen is the chart monomial at the chart
point of that subopen. -/
theorem incChartMonomialFunction_restrict (σ : V → Bool) (e : E) (ab : Fin 2 × Fin 2)
    (W : (vertexScheme ℂ V).Opens) (hW : W ≤ incChartOpen V σ) :
    (vertexScheme ℂ V).presheaf.map (homOfLE hW).op (G.incChartMonomialFunction σ e ab) =
      G.incChartMonomial σ (incChartPoint σ W hW) e ab :=
  G.map_incChartMonomial ((vertexScheme ℂ V).presheaf.map (homOfLE hW).op).hom σ _ e ab

/-- The local entry of the evaluation map for the coefficient `c_{e,α,β}` on chart `σ`:
multiplication by the chart monomial followed by the inverse chart frame of `L_e`. -/
noncomputable def incEntryLocal (e : E) (ab : Fin 2 × Fin 2) (σ : V → Bool) :
    SheafOfModules.unit ((vertexScheme ℂ V).ringCatSheaf.over (incChartOpen V σ)) ⟶
      (G.edgeLineSheaf ℂ e).over (incChartOpen V σ) :=
  moduleOverMultiplication (vertexScheme ℂ V) (incChartOpen V σ)
      ((incChartOpen V σ).topIso.inv (G.incChartMonomialFunction σ e ab)) ≫
    (vertexTwistOverChartIso ℂ V (fun v => (G.endCount e v : ℤ)) (vertexBooleanPivot V σ)).inv

/-- **The local entry in the chart frame.** On a subopen `W` of chart `σ`, the chart coefficient
of the entry applied to a function `x` is `x` times the chart monomial at the chart point. -/
theorem incEntryLocal_coefficient (e : E) (ab : Fin 2 × Fin 2) (σ : V → Bool)
    (W : (vertexScheme ℂ V).Opens) (hW : W ≤ incChartOpen V σ) (x : Γ(vertexScheme ℂ V, W)) :
    vertexTwistSheafChartCoefficient ℂ V (fun v => (G.endCount e v : ℤ)) (vertexBooleanPivot V σ)
        W hW (((G.incEntryLocal e ab σ).val.app (op (Over.mk (homOfLE hW)))).hom x) =
      x * G.incChartMonomial σ (incChartPoint σ W hW) e ab := by
  let F := vertexTwistOverChartIso ℂ V (fun v => (G.endCount e v : ℤ)) (vertexBooleanPivot V σ)
  let m := moduleOverMultiplication (vertexScheme ℂ V) (incChartOpen V σ)
      ((incChartOpen V σ).topIso.inv (G.incChartMonomialFunction σ e ab))
  have h := congrArg (fun φ => (φ.val.app (op (Over.mk (homOfLE hW)))).hom
    ((m.val.app (op (Over.mk (homOfLE hW)))).hom x)) F.inv_hom_id
  change (F.hom.val.app (op (Over.mk (homOfLE hW)))).hom
    ((F.inv.val.app (op (Over.mk (homOfLE hW)))).hom ((m.val.app (op (Over.mk (homOfLE hW)))).hom x)) = _
  refine h.trans ?_
  change (show Γ(vertexScheme ℂ V, W) from (m.val.app (op (Over.mk (homOfLE hW)))).hom x) = _
  rw [moduleOverMultiplication_app, moduleOverMultiplicationCoefficient_geometric,
    Iso.inv_hom_id_apply]
  congr 1
  exact G.incChartMonomialFunction_restrict σ e ab W hW

end Entries

/-! ### The local entries agree on overlaps -/

section Overlaps

/-- Chart coefficients depend only on the chart, not on the term naming it. -/
theorem vertexTwistSheafChartCoefficient_congr (a : V → ℤ) {σ₁ σ₂ : V → Fin 2} (h : σ₁ = σ₂)
    (W : (vertexScheme ℂ V).Opens) (h₁ : W ≤ vertexChartOpen ℂ V σ₁)
    (h₂ : W ≤ vertexChartOpen ℂ V σ₂) (y : Γ(vertexTwistSheaf ℂ V a, W)) :
    vertexTwistSheafChartCoefficient ℂ V a σ₁ W h₁ y =
      vertexTwistSheafChartCoefficient ℂ V a σ₂ W h₂ y := by
  subst h
  rfl

/-- Pair transition coefficients restrict to pair transition coefficients. -/
theorem vertexTwistSheafPairTransitionCoefficient_restrict (a : V → ℤ) (σ τ : V → Fin 2)
    {W W' : (vertexScheme ℂ V).Opens} (h : W' ≤ W) (hW : W ≤ vertexChartPairOpen ℂ V σ τ) :
    vertexTwistSheafPairTransitionCoefficient ℂ V a σ τ W' (h.trans hW) =
      (vertexScheme ℂ V).presheaf.map (homOfLE h).op
        (vertexTwistSheafPairTransitionCoefficient ℂ V a σ τ W hW) := by
  rw [vertexTwistSheafPairTransitionCoefficient, vertexTwistSheafPairTransitionCoefficient,
    moduleOverMultiplicationCoefficient_geometric, moduleOverMultiplicationCoefficient_geometric]
  exact (incPresheaf_restrict_restrict _ _ _ _).symm

/-- The chart monomial of the face's own chart `faceOrientation r`, as a function on the face
open of `r`. -/
noncomputable def incFaceMonomialFunction (r : V → Fin 3) (e : E) (ab : Fin 2 × Fin 2) :
    Γ(vertexScheme ℂ V, incFaceOpen V r) :=
  (vertexFaceSectionsEquiv ℂ V r).symm
    (G.incChartMonomial (faceOrientation r) (faceVariable ℂ r) e ab)

/-- **The local entries in a face frame.** Let `r` be a face refined by chart `σ`. On every
subopen `W` of the face open of `r`, the entry of chart `σ` applied to `x`, read in the frame of
the face's own chart, is `x` times the face monomial: it does not depend on `σ`. This uses the
transition coefficients of `edgeLineSheaf` (`edgeLineSheaf_pairTransition`) and the overlap
formula `incChartMonomial_overlapPoint` for the chart monomials. -/
theorem incEntryLocal_faceCoefficient {σ : V → Bool} {r : V → Fin 3}
    (hσ : FaceRefines (chartFace σ) r) (e : E) (ab : Fin 2 × Fin 2) (W : (vertexScheme ℂ V).Opens)
    (hW : W ≤ incFaceOpen V r) (x : Γ(vertexScheme ℂ V, W)) :
    vertexTwistSheafChartCoefficient ℂ V (fun v => (G.endCount e v : ℤ))
        (vertexBooleanPivot V (vertexFaceBaseChoice V r)) W (hW.trans (incFaceOpen_le_baseChart r))
        (((G.incEntryLocal e ab σ).val.app
          (op (Over.mk (homOfLE (hW.trans (incFaceOpen_le_chart hσ)))))).hom x) =
      x * (vertexScheme ℂ V).presheaf.map (homOfLE hW).op (G.incFaceMonomialFunction r e ab) := by
  let a : V → ℤ := fun v => (G.endCount e v : ℤ)
  let y := ((G.incEntryLocal e ab σ).val.app
    (op (Over.mk (homOfLE (hW.trans (incFaceOpen_le_chart hσ)))))).hom x
  let T := vertexTwistSheafPairTransitionCoefficient ℂ V a
    (vertexBooleanPivot V (vertexFaceBaseChoice V (chartFace σ)))
    (vertexBooleanPivot V (vertexFaceBaseChoice V r)) (incFaceOpen V r)
    (vertexFaceRefinement_le_pair ℂ V hσ)
  let M := G.incFaceMonomialFunction r e ab
  have hpair := vertexTwistSheafChartCoefficient_pair_transition ℂ V a _ _ W
    (hW.trans (vertexFaceRefinement_le_pair ℂ V hσ)) y
  rw [vertexTwistSheafChartCoefficient_congr a
      (congrArg (vertexBooleanPivot V) (vertexFaceBaseChoice_chartFace σ)) W _
      (hW.trans (incFaceOpen_le_chart hσ)),
    incEntryLocal_coefficient, vertexTwistSheafPairTransitionCoefficient_restrict a _ _ hW
      (vertexFaceRefinement_le_pair ℂ V hσ)] at hpair
  have hm : G.incChartMonomial σ (incChartPoint σ W (hW.trans (incFaceOpen_le_chart hσ))) e ab =
      (vertexScheme ℂ V).presheaf.map (homOfLE hW).op
        (G.incChartMonomial σ (incChartPoint σ (incFaceOpen V r) (incFaceOpen_le_chart hσ)) e ab) := by
    rw [G.map_incChartMonomial ((vertexScheme ℂ V).presheaf.map (homOfLE hW).op).hom]
    congr 1
    funext v
    exact (incChartPoint_restrict σ hW _ v).symm
  have hT : vertexFaceSectionsEquiv ℂ V r T = (G.incOverlapEdgeUnit hσ e : FaceRing ℂ r) :=
    G.edgeLineSheaf_pairTransition hσ e
  have hWr : G.incChartMonomial σ (incChartPoint σ (incFaceOpen V r) (incFaceOpen_le_chart hσ)) e ab =
      T * M := by
    apply (vertexFaceSectionsEquiv ℂ V r).injective
    rw [map_mul, hT]
    change _ = _ * (vertexFaceSectionsEquiv ℂ V r) ((vertexFaceSectionsEquiv ℂ V r).symm _)
    rw [RingEquiv.apply_symm_apply, G.map_incChartMonomial (vertexFaceSectionsEquiv ℂ V r)]
    simp_rw [vertexFaceSectionsEquiv_incChartPoint hσ]
    exact G.incChartMonomial_overlapPoint hσ e ab
  have hu : IsUnit ((vertexScheme ℂ V).presheaf.map (homOfLE hW).op T) := by
    apply IsUnit.map
    have hT' : T = (vertexFaceSectionsEquiv ℂ V r).symm (G.incOverlapEdgeUnit hσ e : FaceRing ℂ r) := by
      rw [← hT, RingEquiv.symm_apply_apply]
    rw [hT']
    exact (Units.isUnit _).map _
  rw [hm, hWr, map_mul] at hpair
  apply hu.mul_left_inj.mp
  change _ = (x * (vertexScheme ℂ V).presheaf.map (homOfLE hW).op M) * _
  rw [← hpair]
  ring

/-- **The local entries agree on chart overlaps.** For any two charts `σ` and `τ`, the local
entries of the coefficient `c_{e,α,β}` agree on every subopen of the overlap: both have the same
coefficient in the frame of the face `faceJoin (chartFace σ) (chartFace τ)`. -/
theorem incEntryLocal_compatible (e : E) (ab : Fin 2 × Fin 2) :
    TopCat.Presheaf.IsCompatible (X := TopCat.of (vertexScheme ℂ V))
      (moduleHomSheaf (vertexScheme ℂ V) (SheafOfModules.unit (vertexScheme ℂ V).ringCatSheaf)
        (G.edgeLineSheaf ℂ e)).obj (incChartOpen V)
      (fun σ => moduleOverHomSection (vertexScheme ℂ V) _ _ (incChartOpen V σ)
        (G.incEntryLocal e ab σ)) := by
  intro σ τ
  apply BPFixedPoints.PresheafOfModules.InternalHom.naturalFamilies_ext
  intro Y j x
  have hY : Y.unop ≤ incChartOpen V σ ⊓ incChartOpen V τ := j.unop.le
  have hYr : Y.unop ≤ incFaceOpen V (faceJoin (chartFace σ) (chartFace τ)) :=
    hY.trans (incChartOpen_inf_le_faceJoin σ τ)
  change ((G.incEntryLocal e ab σ).val.app (op (Over.mk (homOfLE
      (hYr.trans (incFaceOpen_le_chart (faceRefines_join_left _ _))))))).hom x =
    ((G.incEntryLocal e ab τ).val.app (op (Over.mk (homOfLE
      (hYr.trans (incFaceOpen_le_chart (faceRefines_join_right _ _))))))).hom x
  apply (vertexTwistChartCoefficientEquiv ℂ V (fun v => (G.endCount e v : ℤ)) _ Y.unop
    (hYr.trans (incFaceOpen_le_baseChart _))).injective
  rw [vertexTwistChartCoefficientEquiv_apply, vertexTwistChartCoefficientEquiv_apply,
    G.incEntryLocal_faceCoefficient (faceRefines_join_left _ _) e ab Y.unop hYr,
    G.incEntryLocal_faceCoefficient (faceRefines_join_right _ _) e ab Y.unop hYr]

end Overlaps

/-! ### The glued evaluation map -/

section Gluing

/-- **The entry `O → L_e` of the evaluation map for the coefficient `c_{e,α,β}`**, glued from the
local entries with `moduleHomGlue`. -/
noncomputable def incEntrySheafMap (e : E) (ab : Fin 2 × Fin 2) :
    SheafOfModules.unit (vertexScheme ℂ V).ringCatSheaf ⟶ G.edgeLineSheaf ℂ e :=
  moduleHomGlue (vertexScheme ℂ V) (SheafOfModules.unit (vertexScheme ℂ V).ringCatSheaf)
    (G.edgeLineSheaf ℂ e) (incChartOpen V) (incChartOpen_iSup_top V)
    (fun σ => G.incEntryLocal e ab σ) (G.incEntryLocal_compatible e ab)

/-- The glued entry restricts on each chart to the local entry. -/
theorem incEntrySheafMap_over (e : E) (ab : Fin 2 × Fin 2) (σ : V → Bool) :
    (SheafOfModules.overFunctor _ (incChartOpen V σ)).map (G.incEntrySheafMap e ab) =
      G.incEntryLocal e ab σ :=
  moduleHomGlue_over (vertexScheme ℂ V) (SheafOfModules.unit (vertexScheme ℂ V).ringCatSheaf)
    (G.edgeLineSheaf ℂ e) (incChartOpen V) (incChartOpen_iSup_top V)
    (fun σ => G.incEntryLocal e ab σ) (G.incEntryLocal_compatible e ab) σ

/-- On a subopen of chart `σ`, the glued entry is the local entry of `σ`. -/
theorem incEntrySheafMap_app (e : E) (ab : Fin 2 × Fin 2) (σ : V → Bool)
    (W : (vertexScheme ℂ V).Opens) (hW : W ≤ incChartOpen V σ) (x : Γ(vertexScheme ℂ V, W)) :
    ((G.incEntrySheafMap e ab).val.app (op W)).hom x =
      ((G.incEntryLocal e ab σ).val.app (op (Over.mk (homOfLE hW)))).hom x :=
  congrArg (fun φ => (φ.val.app (op (Over.mk (homOfLE hW)))).hom x) (G.incEntrySheafMap_over e ab σ)

/-- The glued entry in the chart frame: `x ↦ x · X_{fst e,α}(t) X_{snd e,β}(t)`. -/
theorem incEntrySheafMap_coefficient (e : E) (ab : Fin 2 × Fin 2) (σ : V → Bool)
    (W : (vertexScheme ℂ V).Opens) (hW : W ≤ incChartOpen V σ) (x : Γ(vertexScheme ℂ V, W)) :
    vertexTwistSheafChartCoefficient ℂ V (fun v => (G.endCount e v : ℤ)) (vertexBooleanPivot V σ)
        W hW (((G.incEntrySheafMap e ab).val.app (op W)).hom x) =
      x * G.incChartMonomial σ (incChartPoint σ W hW) e ab := by
  rw [G.incEntrySheafMap_app e ab σ W hW]
  exact G.incEntryLocal_coefficient e ab σ W hW x

end Gluing

/-! ### The evaluation map and its chart form -/

section Evaluation

/-- The sections of a finite biproduct of sheaves of modules on a scheme, as a module over the
functions on the open: the families of sections of the summands. -/
noncomputable def schemeBiproductSectionsEquiv {X : Scheme.{0}} {ι : Type*} [Fintype ι]
    (f : ι → SheafOfModules X.ringCatSheaf) [HasBiproduct f] (W : X.Opens) :
    Γ(⨁ f, W) ≃ₗ[Γ(X, W)] (∀ i, Γ(f i, W)) where
  toFun := biproductSectionsEquiv f (op W)
  map_add' := (biproductSectionsEquiv f (op W)).map_add
  map_smul' := (biproductSectionsEquiv f (op W)).map_smul
  invFun := (biproductSectionsEquiv f (op W)).symm
  left_inv := (biproductSectionsEquiv f (op W)).left_inv
  right_inv := (biproductSectionsEquiv f (op W)).right_inv

/-- The components of a section of a biproduct are its projections. -/
@[simp] theorem schemeBiproductSectionsEquiv_apply {X : Scheme.{0}} {ι : Type*} [Fintype ι]
    (f : ι → SheafOfModules X.ringCatSheaf) [HasBiproduct f] (W : X.Opens) (x : Γ(⨁ f, W)) (i : ι) :
    schemeBiproductSectionsEquiv f W x i = ((biproduct.π f i).val.app (op W)).hom x :=
  rfl

variable (V E) in
/-- The trivial bundle `O^{4m} = B_G ⊗ O_{X_G}`: the finite biproduct of copies of the structure
sheaf, one for each coefficient `c_{e,α,β}`. -/
noncomputable abbrev incCoeffSheaf : SheafOfModules (vertexScheme ℂ V).ringCatSheaf :=
  ⨁ fun _ : IncCoeffIdx E => SheafOfModules.unit (vertexScheme ℂ V).ringCatSheaf

/-- **The evaluation map `O^{4m} → F_G` as a morphism of sheaves of modules on `X_G`.** Its
component in the summand `L_e` of `F_G = G.edgeBundle ℂ` is `Σ_{α,β} c_{e,α,β} · s_{e,α,β}`, where
`s_{e,α,β} = incEntrySheafMap e (α, β)` is glued from the chart monomials. -/
noncomputable def incEvaluationSheafMap : incCoeffSheaf V E ⟶ G.edgeBundle ℂ :=
  biproduct.lift fun e => ∑ ab : Fin 2 × Fin 2,
    biproduct.π (fun _ : IncCoeffIdx E => SheafOfModules.unit (vertexScheme ℂ V).ringCatSheaf)
      (e, ab) ≫ G.incEntrySheafMap e ab

/-- The component of the evaluation map in the summand `L_e`, on sections. -/
theorem incEvaluationSheafMap_π_app (e : E) (W : (vertexScheme ℂ V).Opens)
    (x : (incCoeffSheaf V E).val.obj (op W)) :
    ((biproduct.π (fun e => G.edgeLineSheaf ℂ e) e).val.app (op W)).hom
        ((G.incEvaluationSheafMap.val.app (op W)).hom x) =
      ∑ ab : Fin 2 × Fin 2, ((G.incEntrySheafMap e ab).val.app (op W)).hom
        (((biproduct.π (fun _ : IncCoeffIdx E =>
          SheafOfModules.unit (vertexScheme ℂ V).ringCatSheaf) (e, ab)).val.app (op W)).hom x) := by
  have h := congrArg (fun φ => (φ.val.app (op W)).hom x)
    (biproduct.lift_π (fun e => ∑ ab : Fin 2 × Fin 2,
      biproduct.π (fun _ : IncCoeffIdx E => SheafOfModules.unit (vertexScheme ℂ V).ringCatSheaf)
        (e, ab) ≫ G.incEntrySheafMap e ab) e)
  rw [sheafOfModules_sum_app_apply] at h
  exact h

/-- The chart frame of `F_G` on a subopen `W` of chart `σ`: the chart coefficients of the
components of a section in the summands `L_e`. -/
noncomputable def incEdgeChartEquiv (σ : V → Bool) (W : (vertexScheme ℂ V).Opens)
    (hW : W ≤ incChartOpen V σ) :
    Γ(G.edgeBundle ℂ, W) ≃ₗ[Γ(vertexScheme ℂ V, W)] (E → Γ(vertexScheme ℂ V, W)) :=
  (schemeBiproductSectionsEquiv (fun e => G.edgeLineSheaf ℂ e) W).trans
    (LinearEquiv.piCongrRight fun e =>
      vertexTwistChartCoefficientEquiv ℂ V (fun v => (G.endCount e v : ℤ)) (vertexBooleanPivot V σ)
        W hW)

/-- The chart frame of `F_G` reads the chart coefficient of each component. -/
theorem incEdgeChartEquiv_apply (σ : V → Bool) (W : (vertexScheme ℂ V).Opens)
    (hW : W ≤ incChartOpen V σ) (y : Γ(G.edgeBundle ℂ, W)) (e : E) :
    G.incEdgeChartEquiv σ W hW y e =
      vertexTwistSheafChartCoefficient ℂ V (fun v => (G.endCount e v : ℤ)) (vertexBooleanPivot V σ)
        W hW (((biproduct.π (fun e => G.edgeLineSheaf ℂ e) e).val.app (op W)).hom y) :=
  rfl

/-- The coefficient frame of `O^{4m}` on an open `W`: the components of a section. -/
noncomputable def incCoeffSectionsEquiv (W : (vertexScheme ℂ V).Opens) :
    Γ(incCoeffSheaf V E, W) ≃ₗ[Γ(vertexScheme ℂ V, W)] (IncCoeffIdx E → Γ(vertexScheme ℂ V, W)) :=
  schemeBiproductSectionsEquiv
    (fun _ : IncCoeffIdx E => SheafOfModules.unit (vertexScheme ℂ V).ringCatSheaf) W

/-- **The evaluation map in the chart frame.** On every subopen `W` of the standard chart `σ`,
the evaluation map `O^{4m} → F_G` read in the coefficient frame of `O^{4m}` and the chart frame of
`F_G` is the chart evaluation map `incChartEvaluation σ` of `IncidenceVectorBundleCharts.lean` at
the chart point of `W`. -/
theorem incEvaluationSheafMap_chart (σ : V → Bool) (W : (vertexScheme ℂ V).Opens)
    (hW : W ≤ incChartOpen V σ) (x : Γ(incCoeffSheaf V E, W)) :
    G.incEdgeChartEquiv σ W hW ((G.incEvaluationSheafMap.val.app (op W)).hom x) =
      G.incChartEvaluation σ (incChartPoint σ W hW) (incCoeffSectionsEquiv W x) := by
  funext e
  rw [incEdgeChartEquiv_apply, incEvaluationSheafMap_π_app, map_sum, incChartEvaluation_apply]
  refine Finset.sum_congr rfl fun ab _ => ?_
  exact G.incEntrySheafMap_coefficient e ab σ W hW _

end Evaluation

end BPFixedPoints.Multigraph
